// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(associated_types)]
#![feature(unsafe_destructor)]
#![feature(unboxed_closures)]
#![allow(missing_docs)]

extern crate alloc;

use std::collections::RingBuf;
use std::iter::range_step;
use std::mem;
use std::num::Int;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::ptr::Unique;
use std::rt::heap::{allocate, deallocate};
use std::sync::{Arc, Mutex};

#[inline]
fn round_up(base: uint, align: uint) -> uint {
    (base.checked_add(align - 1)).unwrap() & !(align - 1)
}

/// A faster arena that can hold objects of only one type.
///
/// Safety note: Modifying objects in the arena that have already had their
/// `drop` destructors run can cause leaks, because the destructor will not
/// run again for these objects.
pub struct GCArena<T: Send> {
    inner: Arc<GCArenaInner<T>>
}
impl<T: Send> Clone for GCArena<T> {
    fn clone(&self) -> GCArena<T> {
        GCArena {
            inner: self.inner.clone()
        }
    }
}
unsafe impl<T: Send> Send for GCArena<T> {}
unsafe impl<T> Sync for GCArena<T> {}
struct GCArenaInner<T: Send> {
    /// A pointer to the first arena segment.
    first: Mutex<Unique<GCArenaChunk<T>>>,

    /// A list of free members, stored as raw pointers.
    freelist: Mutex<RingBuf<Unique<T>>>,
}

pub struct GCArenaAllocation<T> {
    ptr: Unique<T>,
    arena: Arc<GCArenaInner<T>>
}

#[unsafe_destructor]
impl<T: Send> Drop for GCArenaAllocation<T> {
    fn drop(&mut self) {
        let mut ptr = Unique::null();
        mem::swap(&mut ptr, &mut self.ptr);

        unsafe {
            drop(ptr::read(ptr.0));
        }

        if let Ok(mut freelist) = self.arena.freelist.lock() {
            freelist.push_front(ptr);
        }
    }
}
impl<T> Deref for GCArenaAllocation<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr.0 }
    }
}
impl<T> DerefMut for GCArenaAllocation<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr.0 }
    }
}

struct GCArenaChunk<T: Send> {
    /// Pointer to the next arena segment.
    next: *mut GCArenaChunk<T>,

    /// The number of elements that this chunk can hold.
    capacity: uint,

    // Objects follow here, suitably aligned.
}
unsafe impl<T: Send> Send for GCArenaChunk<T> {}

fn calculate_size<T: Send>(capacity: uint) -> uint {
    let mut size = mem::size_of::<GCArenaChunk<T>>();
    size = round_up(size, mem::min_align_of::<T>());
    let elem_size = mem::size_of::<T>();
    let elems_size = elem_size.checked_mul(capacity).unwrap();
    size = size.checked_add(elems_size).unwrap();
    size
}

impl<T: Send> GCArenaChunk<T> {
    #[inline]
    unsafe fn new(next: *mut GCArenaChunk<T>, capacity: uint)
           -> *mut GCArenaChunk<T> {
        let size = calculate_size::<T>(capacity);
        let chunk = allocate(size, mem::min_align_of::<GCArenaChunk<T>>())
                    as *mut GCArenaChunk<T>;
        if chunk.is_null() { alloc::oom() }
        (*chunk).next = next;
        (*chunk).capacity = capacity;
        chunk
    }

    /// Destroys this arena chunk. Note that this does not run destructors!
    /// Instead, they run when the smart pointers returned by GCArena.alloc() are destroyed.
    #[inline]
    unsafe fn destroy(&mut self) {
        // Destroy the next chunk.
        let next = self.next;
        let size = calculate_size::<T>(self.capacity);
        deallocate(self as *mut GCArenaChunk<T> as *mut u8, size,
                   mem::min_align_of::<GCArenaChunk<T>>());
        if !next.is_null() {
            (*next).destroy();
        }
    }

    // Returns a pointer to the first allocated object.
    #[inline]
    fn start(&self) -> *const u8 {
        let this: *const GCArenaChunk<T> = self;
        unsafe {
            mem::transmute(round_up(this.offset(1) as uint,
                                    mem::min_align_of::<T>()))
        }
    }

    // Returns a pointer to the end of the allocated space.
    #[inline]
    fn end(&self) -> *const u8 {
        unsafe {
            let size = mem::size_of::<T>().checked_mul(self.capacity).unwrap();
            self.start().offset(size as int)
        }
    }

    /// Iterates over a uint representing the address of each "spot"
    /// in this chunk in which an object could be allocated.
    /// It would be a pointer, but I have no idea how unboxed closures work
    fn iter(&self) -> std::iter::RangeStep<uint> {
        range_step(
            self.start() as uint,
            self.end() as uint,
            mem::size_of::<T>()
        )
    }
}

impl<T: Send> GCArena<T> {
    /// Creates a new `GCArena` with preallocated space for eight objects.
    #[inline]
    pub fn new() -> GCArena<T> {
        GCArena::with_capacity(8)
    }

    /// Creates a new `GCArena` with preallocated space for the given number of
    /// objects.
    #[inline]
    pub fn with_capacity(capacity: uint) -> GCArena<T> {
        unsafe {
            let chunk = GCArenaChunk::<T>::new(ptr::null_mut(), capacity);
            let freelist = (*chunk).iter().map(|x| Unique(x as *mut T)).collect();
            GCArena { inner: Arc::new(GCArenaInner {
                first: Mutex::new(Unique(chunk)),
                freelist: Mutex::new(freelist)
            })}
        }
    }

    /// Allocates an object in the `GCArena`, returning a reference to it.
    #[inline]
    pub fn alloc(&self, object: T) -> GCArenaAllocation<T> {
        let ptr = {
            let ptr;
            loop {
                let maybe_ptr = {
                    let mut freelist = self.inner.freelist.lock().unwrap();
                    freelist.pop_front()
                };
                if let Some(free_ptr) = maybe_ptr {
                    ptr = free_ptr;
                    break;
                } else {
                    self.grow();
                }
            }
            ptr
        };


        let ptr: &mut T = unsafe {
            let ptr: &mut T = mem::transmute(ptr);
            ptr::write(ptr, object);
            ptr
        };

        GCArenaAllocation {
            ptr: Unique(ptr),
            arena: self.inner.clone()
        }
    }

    /// Grows the arena.
    #[inline(never)]
    fn grow(&self) {
        unsafe {
            let mut chunk_lock = self.inner.first.lock().unwrap();
            let new_capacity = (*chunk_lock.0).capacity.checked_mul(2).unwrap();
            let chunk = GCArenaChunk::<T>::new(chunk_lock.0, new_capacity);
            *chunk_lock = Unique(chunk);
            
            self.inner.freelist.lock().unwrap().extend((*chunk).iter().map(|x| Unique(x as *mut T)));
        }
    }
}

#[unsafe_destructor]
impl<T: Send> Drop for GCArenaInner<T> {
    fn drop(&mut self) {
        unsafe {
            // Pass that to the `destroy` method.
            (*self.first.lock().unwrap().0).destroy()
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use self::test::Bencher;
    use super::GCArena;

    #[allow(dead_code)]
    struct Point {
        x: int,
        y: int,
        z: int,
    }

    #[test]
    pub fn test_arena() {
        let arena = GCArena::new();
        for _ in range(0u, 100000) {
            arena.alloc(Point {
                x: 1,
                y: 2,
                z: 3,
            });
        }
    }

    #[bench]
    pub fn bench(b: &mut Bencher) {
        let arena = GCArena::new();
        b.iter(|| {
            arena.alloc(Point {
                x: 1,
                y: 2,
                z: 3,
            })
        })
    }

    #[bench]
    pub fn bench_nonarena(b: &mut Bencher) {
        b.iter(|| {
            box Point {
                x: 1,
                y: 2,
                z: 3,
            }
        })
    }

    #[test]
    pub fn try_to_segfault() {
        let alloc = {
            let arena = GCArena::new();
            arena.alloc(42u64)
        };

        assert_eq!(*alloc, 42);
    }
}
