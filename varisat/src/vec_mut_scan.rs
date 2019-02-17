//! Forward scan over a vector with mutation and item removal.

use std::ops::{Deref, DerefMut};
use std::{mem, ptr};

/// Forward scan over a vector with mutation and item removal.
///
/// Provides an iterator like interface over a vector which allows mutation and removal of items.
/// Items are kept in order and every item is moved at most once, even when items are removed.
/// Dropping the `VecMutScan` mid-iteration keeps remaining items in the vector.
///
/// This does not implement the iterator trait, as the returned items borrow from this (i.e. this is
/// a streaming iterator).
///
/// The [`next`](VecMutScan::next) method returns [`VecMutScanItem`] values, which auto dereference
/// to the vector's item type but also provide a [`remove`](VecMutScanItem::remove) and
/// [`replace`](VecMutScanItem::replace) method.
pub struct VecMutScan<'a, T: 'a> {
    vec: &'a mut Vec<T>,
    base: *mut T,
    write: usize,
    read: usize,
    end: usize,
}

// TODO replace indices with pointers when pointer offset computation is stabilized should
// benchmarks show an improvement.

impl<'a, T: 'a> VecMutScan<'a, T> {
    pub fn new(vec: &mut Vec<T>) -> VecMutScan<T> {
        let base = vec.as_mut_ptr();
        let write = 0;
        let read = 0;
        let end = vec.len();

        // Make sure vec is consistent when we are leaked (leak amplification).
        unsafe {
            vec.set_len(0);
        }

        VecMutScan {
            vec,
            base,
            write,
            read,
            end,
        }
    }

    pub fn next<'s>(&'s mut self) -> Option<VecMutScanItem<'s, 'a, T>> {
        if self.read != self.end {
            Some(VecMutScanItem { scan: self })
        } else {
            None
        }
    }
}

impl<'a, T: 'a> Drop for VecMutScan<'a, T> {
    fn drop(&mut self) {
        unsafe {
            let tail_len = self.end - self.read;
            ptr::copy(
                self.base.add(self.read),
                self.base.add(self.write),
                tail_len,
            );
            self.vec.set_len(self.write + tail_len);
        }
    }
}

/// Reference wrapper that enables item removal for [`VecMutScan`].
pub struct VecMutScanItem<'s, 'a, T: 'a> {
    scan: &'s mut VecMutScan<'a, T>,
}

impl<'s, 'a, T: 'a> VecMutScanItem<'s, 'a, T> {
    /// Removes and returns this item from the vector.
    pub fn remove(self) -> T {
        unsafe {
            let result = ptr::read(self.scan.base.add(self.scan.read));
            self.scan.read += 1;
            mem::forget(self);
            result
        }
    }

    /// Replaces this item with a new value.
    ///
    /// This is equivalent to assigning a new value using [`DerefMut`], but can avoid an
    /// intermediate move within the vector's storage.
    pub fn replace(self, value: T) {
        unsafe {
            // This read is required to drop the replaced value
            ptr::read(self.scan.base.add(self.scan.read));

            ptr::write(self.scan.base.add(self.scan.write), value);
            self.scan.read += 1;
            self.scan.write += 1;
            mem::forget(self);
        }
    }
}

impl<'s, 'a, T: 'a> Deref for VecMutScanItem<'s, 'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.scan.base.add(self.scan.read) }
    }
}

impl<'s, 'a, T: 'a> DerefMut for VecMutScanItem<'s, 'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.scan.base.add(self.scan.read) }
    }
}

impl<'s, 'a, T: 'a> Drop for VecMutScanItem<'s, 'a, T> {
    fn drop(&mut self) {
        unsafe {
            ptr::copy(
                self.scan.base.add(self.scan.read),
                self.scan.base.add(self.scan.write),
                1,
            );
            self.scan.read += 1;
            self.scan.write += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;

    use proptest::*;

    #[test]
    fn check_item_drops() {
        let mut input: Vec<_> = vec![0, 1, 2, 3, 4, 5, 6]
            .into_iter()
            .map(|v| Rc::new(v))
            .collect();
        let input_copy = input.clone();

        let mut scan = VecMutScan::new(&mut input);

        let mut keep = None;

        while let Some(item) = scan.next() {
            if **item == 2 {
                item.replace(Rc::new(10));
            } else if **item == 3 {
                keep = Some(item.remove());
            } else if **item == 4 {
                item.remove();
            } else if **item == 5 {
                break;
            }
        }

        let ref_counts: Vec<_> = input_copy.iter().map(|rc| Rc::strong_count(rc)).collect();

        assert_eq!(ref_counts, vec![2, 2, 1, 2, 1, 2, 2]);
        assert_eq!(keep.map(|rc| Rc::strong_count(&rc)), Some(2));
    }

    proptest! {
        #[test]
        fn mutate_and_remove(input in collection::vec(0..10usize, 0..100)) {
            let mut test = input.clone();
            let mut scan = VecMutScan::new(&mut test);
            let mut input_iter = input.iter().cloned();
            while let Some(mut item) = scan.next() {
                let value = *item;
                prop_assert_eq!(input_iter.next(), Some(value));
                if value == 0 {
                    item.replace(10);
                } else if value < 5 {
                    prop_assert_eq!(item.remove(), value);
                } else if value == 9 {
                    break;
                } else {
                    *item *= 2;
                }
            }
            drop(scan);

            let mut found_9 = false;

            let expected: Vec<_> = input
                .iter()
                .flat_map(|&value| {
                    if found_9 {
                        Some(value)
                    } else if value == 0 {
                        Some(10)
                    } else if value < 5 {
                        None
                    } else if value == 9 {
                        found_9 = true;
                        Some(value)
                    } else {
                        Some(value * 2)
                    }
                })
                .collect();

            prop_assert_eq!(test, expected);
        }
    }
}
