//! This module introduces the data structures to speedup comparison between
//! objects of a known set, whose Ord::cmp is expensive.
//!
//! A plain unsigned integer is assigned to each object of the set, where
//! Ord::cmp between two integers matches the Ord::cmp between the objects of
//! the set. The idea is that comparing unsigned ints is much cheaper than
//! comparing the objects themselves.
//!
//! This is used to speedup the comparison between signature to monomial ratios
//! in the signature Buchberger algorithm.

use std::collections::BTreeMap;

/// Maps an object to a comparer that compares with the same Ord with the
/// other objects in the map.
pub struct ComparerMap<T: Ord + Clone>(BTreeMap<T, u32>);

impl<T: Ord + Clone> ComparerMap<T> {
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Maybe returns the corresponding comparer for a value, possibly storing
    /// a copy of value internally. If not possible to assign an comparer to
    /// the value, returns None, on which case the map needs to be rebuilt.
    fn get_comparer(&mut self, value: &T) -> Result<u32, ()> {
        // Get the upper bound element.
        let upper = self.0.range(value..).next();
        // Test if it is a match, and extract the value as i64 (if None, it is u32::MAX + 1).
        let upper = if let Some((v, comparer)) = upper {
            if v == value {
                return Ok(*comparer);
            }
            *comparer as i64
        } else {
            u32::MAX as i64 + 1
        };

        // Get the lower bound element.
        let lower = self.0.range(..value).next_back();
        // Extract the value as i64 (if None, it is -1).
        let lower = lower.map_or(-1, |(_, comparer)| *comparer as i64);

        // Test if there is at least a number between lower and upper.
        if lower + 1 >= upper {
            return Err(());
        }

        let new_idx = ((lower + upper) / 2) as u32;
        self.0.insert(value.clone(), new_idx);

        Ok(new_idx)
    }

    /// Reassign an index to all known values, spacing the values equidistantly,
    /// so more indices can be assigned.
    ///
    /// All FastCompared objects previously created with this map will no longer
    /// compare correctly with the new objects created after the rebuild.
    pub fn rebuild(&mut self) {
        let len = self.0.len() as u64;
        let num_splits = len + 1;
        for (mul, (_, index)) in (1..=len).zip(self.0.iter_mut()) {
            *index = (mul * (u32::MAX as u64) / num_splits) as u32;
        }
    }
}

/// Struct that holds the object and the comparer.
///
/// The ratio itself is just a signature where the exponents can be negative,
/// but it also includes a comparer value, which, for the same comparerMap,
/// is unique per ratio and compares with the same Ord as the ratio. It is used
/// to speed up the comparison between ratios.
///
/// comparer may be None, in which case the comparison is done by value. This
/// is to allow for comparing without having to compute the comparer. This is
/// only because BTreeMap does not allows to search by predicate.
///
/// TODO: remove the Option, and when using a Ratio object as key in a map, use
/// a map structure that allows for searching by predicate when you don't have
/// the comparer for the value.
#[derive(Debug, Clone)]
pub struct FastCompared<T: Ord + Clone> {
    comparer: Option<u32>,
    value: T,
}

impl<T: Ord + Clone> FastCompared<T> {
    /// Creates a new FastCompared object which correctly fast compares with
    /// other objects from the same comparer_map, if one is provided.
    ///
    /// If comparer_map is None, a new object is returned with comparer set to
    /// None. If comparer_map is not None, and a the comparer could not be
    /// created, None is returned.
    pub fn new(comparer_map: Option<&mut ComparerMap<T>>, value: T) -> Option<Self> {
        Some(Self {
            comparer: comparer_map
                .map(|cm| cm.get_comparer(&value))
                .transpose()
                .ok()?,
            value,
        })
    }

    /// Updates the comparer to be compatible with objects from a different
    /// ComparerMap.
    ///
    /// This must be called after ComparerMap::rebuild() is called, so that self
    /// remains compatible with newly created FastCompared objects.
    ///
    /// Returns Ok(()) if worked, or Err(()) if failed. Should never fail if
    /// called with the same ComparerMap that created the object, even after
    /// ComparerMap::rebuild().
    pub fn update(&mut self, comparer_map: &mut ComparerMap<T>) -> Result<(), ()> {
        self.comparer = Some(comparer_map.get_comparer(&self.value)?);
        Ok(())
    }

    pub fn get_value(&self) -> &T {
        &self.value
    }

    /// Return the stored value.
    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T: Ord + Clone> PartialEq for FastCompared<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self.comparer, other.comparer) {
            (Some(a), Some(b)) => a == b,
            _ => self.value == other.value,
        }
    }
}

impl<T: Ord + Clone> Eq for FastCompared<T> {}

impl<T: Ord + Clone> PartialOrd for FastCompared<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl<T: Ord + Clone> Ord for FastCompared<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.comparer, other.comparer) {
            (Some(a), Some(b)) => a.cmp(&b),
            _ => self.value.cmp(&other.value),
        }
    }
}
