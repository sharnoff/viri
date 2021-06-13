//! A simple LRU cache for values ordered by size (cost) and index

use crate::utils::Never;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use std::collections::BTreeMap;
use std::ops::RangeBounds;

/// A simple LRU cache for values ordered by size (cost) and index
///
/// The central idea for this cache is taken from a 2002 paper detailing a way to handle
/// variable-size items in an LRU cache. There's a couple additions and slight tweaks here, notably
/// with the ability to access values by index, but those are explained in the relevant locations.
///
/// The paper is titled *Optimizing LRU Caching for Variable Document Sizes*, by Jelenkovíc and
/// Radovanovíc. ([link])
///
/// ## More about cost
///
/// When we say "cost" here, we are only referring to the size of object -- i.e. the cost to keep
/// it cached. This can be used in a more advantageous way, however: defining the cost of a value
/// to be larger for values that are easier to recompute will mean that the values that tend to be
/// recomputed will only be the ones for which it is quick to do so.
///
/// [link]: https://www.ee.columbia.edu/~predrag/mypub/LRUsize.pdf
pub struct SizedLruCache<Idx, T> {
    // The amount of cost left available to us. Normally, this value is `Ok` and has the expected
    // meaning. In order to cover the cases where we temporarily overflow the maximum value with an
    // item that's bigger than the maximum cost, we represent the deficit by `Err(c)`
    available_cost: Result<Cost, Cost>,
    max_cost: Cost,

    // Local RNG for generating numbers. This can be a `SmallRng` because it doesn't need to be
    // secure in any way - we just want it to be as fast as possible.
    rng: SmallRng,

    // Mapping of indexes (which may consist of multiple parts) to the values contained there
    //
    // All `ValueId`s used must be valid
    map: BTreeMap<Idx, ValueId>,

    // The actual values used, indexed by `ValueId`. This vector essentially contains two linked
    // lists, with all of the Ok(_) values in one and the Err(_) values in another.
    //
    // We're representing the standard doubly-linked list that we'd use in an LRU cache inside the
    // Ok(_) values by having each `Item` store addresses by `ValueId`. This means we can avoid
    // making many small allocations (i.e. one for each node).
    //
    // The Err(_) values give the list of currently-vacant slots in the vector, due to previous
    // deallocation. Any `Err(Some(id))` points to the next index in the vector that's empty. Note
    // that "next" here doesn't actually imply any particular ordering; the indexes jump around
    // because actually finding the next empty index would be expensive.
    //
    // ---
    // If we were *very* confident in the validity of this datastructure, we could use a union
    // here; there's a lot of "unecessary" unwrapping in order to extract values that we already
    // know are Ok(_) or Err(_)
    values: Vec<Result<Item<Idx, T>, Option<ValueId>>>,

    // The index of the value at the start of the doubly-linked list in `values`
    queue_start: Option<ValueId>,
    // The index of the value at the end of the doubly-linked list in `values`
    queue_end: Option<ValueId>,

    // The first index in `values` matching `Err(_)`.
    first_empty_v_id: Option<ValueId>,
}

// A single value, representing a node in a doubly-linked list
struct Item<Idx, T> {
    prev: Option<ValueId>,
    next: Option<ValueId>,

    index: Idx,
    cost: Cost,
    val: T,
}

// We use a type alias for all internal references to costs, just to minimize the amount of changes
// we'd need to make if we ever changed this. It also helps to be more explicit about the meaning
// of values.
type Cost = u64;

#[derive(Debug, Copy, Clone, PartialEq)]
struct ValueId(usize);

impl<Idx, T> SizedLruCache<Idx, T>
where
    Idx: Clone + Ord,
{
    /// Creates a new cache with the given maximum allowed cost
    ///
    /// We *do* allow the total cost to temporarily exceed the maximum, in the case where an item
    /// has been cached that singularly exceeds it. There will never be more than one such item
    /// stored.
    ///
    /// Costs are always given as a `u64`, for simplicity.
    pub fn new(cost: u64) -> Self {
        SizedLruCache {
            available_cost: Ok(cost),
            max_cost: cost,
            // The initialization of `SmallRng` calls for seeds without many zeroes. `u64::MAX` has
            // no zeroes, and from a small amount of testing, it seems to work fine.
            rng: SmallRng::seed_from_u64(u64::MAX),
            map: BTreeMap::new(),
            values: Vec::new(),
            queue_start: None,
            queue_end: None,
            first_empty_v_id: None,
        }
    }

    /// Produces an iterator over all of the values currently stored in the cache within the range
    ///
    /// This method is typically used in order to determine the information that currently needs
    /// to be added to the cache.
    pub fn get_range<'a>(
        &'a mut self,
        range: impl RangeBounds<Idx> + Clone,
    ) -> impl 'a + Iterator<Item = &'a T> {
        let map_range = self.map.range(range);

        for (_, &v_id) in map_range.clone() {
            Self::try_bump(
                v_id,
                &mut self.values,
                self.max_cost,
                &mut self.rng,
                &mut self.queue_start,
                &mut self.queue_end,
            );
        }

        // TODO-RFC#2229: This results in a particularly strange error if we replace `self_values`
        // by `self.values` in the closure below. Instead of directly complaining about conflicting
        // borrows, we get something about "unable to infer correct lifetime" on the iterator we're
        // returning.
        let self_values = &self.values;
        map_range.map(move |(_, v_id)| &self_values[v_id.0].as_ref().unwrap().val)
    }

    /// Caches the value, possibly removing other values in order to make space
    ///
    /// This method will intentionally do nothing, at random. If you require the particular value
    /// to be present immediately after caching, use the [`insert`] method instead.
    ///
    /// If the cost of the value is greater than or equal to the maximum allowed cost for this
    /// cache, this method will always do nothing. Again, [`insert`] does not follow this.
    ///
    /// ## Panics
    ///
    /// Please note that this method may panic if there is an existing entry with the same index.
    /// Typically, [`get_range`] is used before performing any insertions.
    ///
    /// We also do not allow a cost of zero; this will panic as well.
    ///
    /// [`get_range`]: Self::get_range
    pub fn cache(&mut self, index: Idx, val: T, cost: u64) {
        assert!(cost != 0);

        if cost >= self.max_cost {
            return;
        }

        // If we'd have to remove something in order to make space, randomly choose not to insert.
        if !matches!(self.available_cost, Ok(c) if c >= cost) {
            let prob = Self::prob_for_cost(cost);
            if self.rng.gen::<f32>() > prob {
                return;
            }
        }

        self.insert(index, val, cost);
    }

    /// Inserts the value into the cache, removing other values as necessary to make space
    ///
    /// This method guarantees that the value will be in the cache after calling. If this is not
    /// required, you should use [`cache`], which does not provide this guarantee.
    ///
    /// If the value is too big for the cache, we temporarily accomodate it, removing the value as
    /// soon as a new one is added.
    ///
    /// ## Panics
    ///
    /// Please note that this method will panic if there is an existing entry with the same index.
    /// Typically, [`get_range`] is used before performing any insertions.
    ///
    /// We also do not allow a cost of zero; this will panic as well.
    ///
    /// [`get_range`]: Self::get_range
    pub fn insert(&mut self, index: Idx, val: T, cost: u64) {
        assert!(cost != 0);

        // First, if there was some other value that we temporarily accomodated, we should remove
        // that.
        let mut available_cost = match self.available_cost {
            Ok(c) => c,
            Err(c) => {
                let v_id = self.queue_end.unwrap();
                let item = &self.values[v_id.0].as_ref().unwrap();

                let available_cost = item.cost - c;
                self.available_cost = Ok(available_cost);

                self.map.remove(&item.index);
                self.remove_val(v_id);

                available_cost
            }
        };

        // Now, make room for the value, if possible:
        if cost >= self.max_cost {
            // If the cost is too big to fit either way, we'll store it separately.
            self.available_cost = Err(cost - available_cost);
        } else {
            while available_cost < cost {
                let v_id = self.queue_end.unwrap();
                let item = &self.values[v_id.0].as_ref().unwrap();

                available_cost += item.cost;
                self.map.remove(&item.index);
                self.remove_val(v_id);
            }
        }

        let item = Item {
            prev: None,
            next: self.queue_start,
            index: index.clone(),
            cost,
            val,
        };

        let new_v_id = self.insert_new_v_id(item);

        if let Some(v_id) = self.queue_start {
            self.values[v_id.0].as_mut().unwrap().prev = Some(new_v_id);
        }
        self.queue_start = Some(new_v_id);

        if self.queue_end.is_none() {
            self.queue_end = Some(new_v_id);
        }

        if self.map.insert(index, new_v_id).is_some() {
            panic!("value inserted at duplicate index");
        }
    }

    /// Retrieves the value with the specified index from the cache, if it exists
    ///
    /// We also perform the necessary "bump to the front of the queue" operation, where applicable.
    /// More information is available in the source of the function.
    pub fn get(&mut self, index: Idx) -> Option<&T> {
        // The paper referenced in the type-level docs uses a probabilistic algorithm to
        // *sometimes* move an item to the front of the queue, depending on a particular
        // probability.

        let v_id = self.map.get(&index)?.clone();
        Self::try_bump(
            v_id,
            &mut self.values,
            self.max_cost,
            &mut self.rng,
            &mut self.queue_start,
            &mut self.queue_end,
        );

        Some(&self.values[v_id.0].as_ref().unwrap().val)
    }

    /// (*Internal*) Removes the value with the given id from `self.values`
    ///
    /// Note that this method *only* affects the `values` and associated list-tracking fields; it
    /// does not update the available cost.
    fn remove_val(&mut self, v_id: ValueId) {
        let item = &self.values[v_id.0].as_ref().unwrap();
        if self.queue_end == Some(v_id) {
            self.queue_end = item.prev;
        }

        if self.queue_start == Some(v_id) {
            self.queue_start = item.next;
        }

        self.values[v_id.0] = Err(self.first_empty_v_id);
        self.first_empty_v_id = Some(v_id);
    }

    /// (*Internal*) Finds a `ValueId` at which to insert the item and places it there
    ///
    /// If there aren't any spots left, we push onto the end of the `values` vector
    fn insert_new_v_id(&mut self, item: Item<Idx, T>) -> ValueId {
        match self.first_empty_v_id.take() {
            Some(id) => {
                // If there was a next link in the list of empty values, replace the current head
                self.first_empty_v_id = self.values[id.0]
                    .as_ref()
                    .map(|_| -> Never { panic!("expected `Err` value") })
                    .unwrap_err()
                    .clone();
                self.values[id.0] = Ok(item);
                id
            }
            None => {
                self.values.push(Ok(item));
                ValueId(self.values.len() - 1)
            }
        }
    }

    /// (*Internal*) Helper function to possibly "bump" a value to the front of the queue
    ///
    /// This function will randomly determine whether to bump the value, using the probability
    /// given by [`prob_for_cost`]. We never bump values with cost greater than or equal to
    /// `max_cost`.
    ///
    /// ## Panics
    ///
    /// This method panics if the `ValueId` does not correspond to a currently-active value.
    ///
    /// [`prob_for_cost`]: Self::prob_for_cost
    fn try_bump(
        v_id: ValueId,
        values: &mut [Result<Item<Idx, T>, Option<ValueId>>],
        max_cost: Cost,
        rng: &mut SmallRng,
        queue_start: &mut Option<ValueId>,
        queue_end: &mut Option<ValueId>,
    ) {
        let item = &values[v_id.0].as_ref().unwrap();
        let prev = item.prev;
        let next = item.next;

        let bump_to_front =
            item.cost < max_cost && rng.gen::<f32>() < Self::prob_for_cost(item.cost);

        // Don't do "bump to front" logic if it's already at the front
        if bump_to_front && prev.is_some() {
            values[prev.unwrap().0].as_mut().unwrap().next = next;
            match next {
                None => *queue_end = prev,
                Some(ValueId(i)) => values[i].as_mut().unwrap().prev = prev,
            }

            values[v_id.0].as_mut().unwrap().next = *queue_start;
            *queue_start = Some(v_id);
        }
    }

    /// (*Internal*) Computes the probability of moving value with the given cost to the front of
    /// the queue, whether it's already present in the queue or not
    ///
    /// This probability is also used when deciding whether to insert a value into the cache. It's
    /// based on the function specified in the paper given above.
    fn prob_for_cost(cost: Cost) -> f32 {
        // It's a little tricky tracking down where in the paper the actual function is defined.
        //
        // I found it in Section 4, Theorem 3 (page 11). The central claim is that the probability
        // of "bumping" a value should be inversely proportional to the size of the value. In the
        // paper, they directly say that the probability pₖ = 1/sₖ (for size sₖ). I'm not 100% sure
        // that's the best solution *for this application*, particularly because of the
        // distribution of sizes we're dealing with, but we'll go with it anyways -- it probably
        // doesn't matter *too* much.
        //
        // AND we can always do benchmarking later, if need be :)

        1.0 / cost as f32
    }
}
