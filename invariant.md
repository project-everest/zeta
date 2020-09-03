# An invariant for LowLevelVerifier

Let's start with the simplified setting of only a single verifier thread

Towards the end of this document, we'll discuss how to generalize the
proposed invariant and proof structure to the concurrent setting with
multiple verifier threads.

## High-level state

From the mathematical model, a verifier state contains three main elements:

1. Key-value store, modeled as partial map `key -> option value`

2. An evict set: `ev_set: set (key & value & timestamp)`, where
   `timestamp = (nat & nat)` for a pair of an epoch counter and a
   counter with a total order on timestamps.

3. An add multiset:  `add_set: multiset (key & value & timestamp)`

## Low-level state

Rather than maintaining the high-level state directly (which is
inefficient), the low-level verifier maintains:

1. A slot-record map, represented as `store : array (option record)`
   where the index into the store array is called a "slot id", and
   `record` augments a high-level key/value pair with three additional
   bits.

```
record = {
  record_key:key;
  record_value:value;
  record_add_method:add_method; //MAdd | BAdd
  in_store:direction -> bool; //direction = L | R
}
```

2. An evict set hash: `ev_hash : prf_set_hash`, which accumulates an
   XOR of a PRF of `(key & value & timestamp)` elements.

3. An add set multi hash: `add_hash : prf_set_hash & uint_64`, which
   accumulates an XOR of a PRF of `(key & value & timestamp)`
   elements, together with a total cardinality of the set.

4. A monotonically increasing `clock : timestamp`

## An informal analysis and some intuitions

A central point in a proof of correctness of the low-level verifier is
to maintain a representation invariant relating the low-level state to
the high-level state.

If at every point we can show that the low-level state is in a
bijection with the high-level state, then the proof strategy is to
show that every operation in the low-level verifier simulates the
corresponding operation in the high-level verifier.

That is, ideally we would have a commuting diagram for a lock-step
bisimulation like the following:

```

High:   hst -----------vaddm--------------> hst'
         ^                                   ^
         .                                   .
         .                                   .
        inv                                 inv
         .                                   .
         .                                   .
         v                                   v
Low:    lst -----------vaddm_low----------> lst'

```

However, the situation is not quite so simple.

The main property that we need to establish is that the low-level
store (the record array) can be interpreted as a key-value map. In
particular, it should have no duplicate keys. But, this property is
not easy to establish.

There are two sources of complication.

### Ensuring that adding a Merkle entry does not introduce a duplicate key

The Merkle entries form a sparse binary tree, where each internal node
in the tree is associated with a key and maintains a hash of both its
(not necessarily immediate) descendents. I.e., a Merkle value is

```
(* information about a desc stored in a merkle node *)
type descendent_hash =
  | Empty: descendent_hash
  | Desc: k:key ->
          h:hash_value ->
          evicted_to_blum:bool ->
          descendent_hash

type value =
  | MVal : l:descendent_hash -> r:descendent_hash -> value
  | DVal : data_value -> value
```

When adding a Merkle entry to the store, we need to ensure that the
key associated with the Merkle entry is not already in the store
(since that would make the store no longer a key-value map).

However, the store is indexed only by slot ids and checking that the
key by scanning the entire store is unacceptable performance-wise.

Instead, what we are going to do is rely on the following invariant:

A Merkle entry `r` can be added at slot `me`, supposedly a descendent
of the entry at slot `ancestor'`, only if:

- slot `me` is vacant (easy)

- slot `ancestor` contains a Merkle entry such its descendent hash in
  a given direction `d` records the key of the new entry `r` and the
  ancestor's "in store" bit for `d` is not set. i.e., the invariant
  must capture that when a node's in store bit for `d` is not set,
  then the store does not contain the that node's descendent in
  direction `d`.

#### Splitting a Merkle edge

Consider the following scenario with both `m0` in the store at slots
`s0` and its descendent `m1` may or may not be in the store.

```
      m0: (k0, (k1, h1, b), ...)
      /
     /
    /
   /
   m1: (k1, ...)
```

We have a Merkle node `m0` with key `k0` has in direction `l` a
descendent node `m1` with key `k1`. `m0`'s in-store bit for `k1` may
or may not be set.

Let's say we now want to add a new entry `m` to the store with key `k`
that is a between `k0` and `k1`.

In this setting, we need to split the edge between `m0` and `m1` and
add `m` in between.

To ensure that `m` is not already in the store, our invariant need to
ensure that if `m0` mentions `k1` as its descendent, then `k1` is its
nearest descendent in the entire sparse Merkle tree. So, if we're
adding a `k` between `k` and `k1` then `k` clearly must not exist in
the store either, since the keys in the store are a subset of all the
keys in the entire tree.

### Ensuring that adding a Blum entry does not introduce a duplicate key

In a pure sparse Merkle setting, ensuring that the low-level store
represents a high-level key-value map is a relatively easy structural
property of the Merkle tree augmented with the in-store bits.

However, when Blum entries are considered, the situation is
substantially more subtle.

#### vevictb

Consider evicting a slot `s` with timestamp `t` from the store to Blum.

We do the following:

1. check that slot `s` exists and contains record `r`
2. check that the timestamp `t` exceeds the current clock
3. add `e = (r.record_key, r.record_value, t)` to the evict hash
4. remove `s` from the store
5. advance the clock to at least `t + 1`

This case is easy, since we are removing `s` from the store and so
certainly cannot introduce any duplicate keys.

#### vaddb

Now, consider adding an record `r` with timestamp `t` to the store at
slot `s`, using the Blum method (i.e., `vaddb`).

In this case, we do the following:

1. check that the slot `s` is empty (easy)
2. add `r` at slot `s` (and mark it as `BAdd` for "added to Blum")
3. add `e = (r.record_key, r.record_value, t)` to the `add_hash`
4. advance the clock at least `t + 1`.

In this case, `r.record_key` may actually already be present in the store.

But, in case it is, then the entry `e` cannot be in the current evict
set---since if it is in the evict set, then from the reasoning in the
case of `vevictb`, then it cannot be in the store.

Further, this particular entry cannot be in any extension of the evict
set (since the clock is advanced) ... and so add hash and the evict
hash have diverged and a hash equality check at the end of the epoch
is doomed to fail.

## An attempt at a formal invariant

To describe a low-level invariant, we first define a type `LST` that
encapsulates all the low-level state:

```
type lst =
  | LST:
     clock:timestamp ->
     store:seq (option record) ->
     evict_set:set (key & value & timestamp) ->
     add_mset:multiset (key & value & timestamp) ->
     lst
```

Next, we define a preorder that constrains how the low-level state is
allowed to evolve, i.e., the clock is increasing, the evict and add
sets are increasing, and every element added to the evict set in the
future has a timestamp strictly greater than the current clock.

```
let evolves : preorder lst = fun l0 l1 ->
    l0.clock <= l1.clock /\
    l1.evict_set >= l0.evict_set /\
    l1.add_mset >= l0.add_mset /\
    (forall e in (l1.evict_set \ l0.evict_set). e.timestamp > l0.clock)
```

Every function in the Veritas interface is shown to evolve the state
according this preorder (but we won't be using any F* theory of
monotonicity or anything like that).

Then, a notion of compatibility of add and evict sets, i.e., every
element in the add set is also in the evict set.

```
let eac evict_set add_mset =
    //1. the add multi-set is really a set
    (forall e. cardinality e in add_mset <= 1) /\
    //2. every element in the add set is also in the evict set
    (forall e. e in add_mset ==> e in evict_set) /\
    //3. every element in the evict set has a unique timestamp
    (forall e0 e1 in evict_set. e0 <> e1 ==> e0.timestamp <> e1.timestamp) /\
    //4. entries can be added at timestamp t1 only if evicted entries at
    //   earlier timestamps have also been added
    (forall {(k, _, t1)} in add_mset.
            {(k, _, t0)} in evict_set.
            t0 <= t1 ==> exists (k, _, t0) in add_mset)
```

Next, a store invariant:

```
let store_is_map store =
    //1. keys are unique
    (forall s0 s1 in store. store[s0].record_key <> store[s1].record_key) /\
    //2. in store bits unset means that descendent is not in store
    (forall s in store, (d:direction).
         let r = store[s] in
         let dh = descendent d r in
         not (r.in_store d) ==>
         (forall s' in store. store[s'].record_key <> dh.key)) /\
    //3. descendent edges are to the nearest descendent
    (forall s in store, (d:direction).
        let r = store [s] in
        let dh = descendent d r in
        (forall s' in store.
            not (dh.key < store[s'].record_key < r.record_key)))
```

When a store is a map, then it can be transformed to a map:

```
val as_map (s:store{store_is_map s}) : key -> option value
```

Finally, relating the evict/add sets to the store

```
let max_timestamp_of k s ts =
    (exists (k, v, ts) in s) /\
    (forall (k, v', ts') in s. ts' <= ts)

//if a record was most recently evicted, then its key is not in the store
let store_evict_add store evict_set add_set =
    forall key evict_ts add_ts.
        max_timestamp_of key evict_set evict_ts /\
        max_timestamp_of key add_set add_ts /\
        evict_ts > add_ts ==>
        (forall s in store. store[s].record_key <> key)
```

Putting it together:

```
let invariant (LST clock store evict_set add_mset) =
    //1. the clock bounds the timestamps of all entries in both sets
    (forall k. max_timestamp_of k evict_set < clock /\
               max_timestamp_of k add_set < clock) /\
    //2. most recently evicted keys are definitly not in the store
    store_evict_add store evict_set add_mset /\
    //3. if the sets are eac, then the store is a map
    (eac evict_set add_mset ==> store_is_map store) /\
```

We should be able to prove a lemma of the following form, i.e., once
eac is violated it cannot be restored.

```
val eac_violation_is_final (lst:lst{invariant lst})
    : Lemma
      ((exists e. e in lst.add_mst /\
                  e not-in evict_set /\
                  e.timestamp < lst.clock) ==>
       (forall lst'. invariant lst' /\ evolves lst lst' ==>
                  not (eac lst'.evict_set lst'.add_set)))
```

Now, connecting the low-level concrete state to the invariant is relatively easy

```
type concrete_state =
  | CST :  clk:ref timestamp
        -> st:array (option record)
        -> evict_hash:prf_set_hash
        -> evict_set: ref (erased (set (key & value & timestamp)))
        -> add_hash:(prf_set_hash & ref u64)
        -> add_mset: ref (erased (mset (key & value & timestamp)))
        -> concrete_state

let as_lst (CST clk st evict_hash evict_set add_hash add_mset)
           (h:HS.mem)
  : lst
  = LST (HS.get clk h)
        (HS.as_seq st h)
        (HS.get evict_set h)
        (HS.get add_set h)

let inv (CST clk st evict_hash evict_set add_hash add_mset)
        (h:HS.mem) =
    invariant (as_lst (CST clk st evict_hash evict_set add_hash add_mset) h) /\
    get_hash_value evict_hash h == set_hash_spec (HS.get evict_set h) /\
    get_hash_value (fst add_hash) h == set_hash_spec (HS.get add_mset h) /\
    HS.get (snd add_hash) h == cardinality (HS.get add_mset h)
```

With this in hand, a specification style for the API is something like:

```
val vaddm (s s':slot_id) (r:record) (cst:concrete_state)
 : StackErr unit
   (requires fun h0 -> inv cst h0)
   (ensures fun h0 _ h1 ->
       inv cst h1 /\
       cst_evolves (as_lst c h0) (as_lst c h1)
       (eac (as_lst cst h0) /\
        eac (as_lst cst h1) ==>
        as_map (as_lst cst h1) == Spec.vaddm ... (as_map (as_lst cst h0))))
```

i.e., so long as the initial and final states are eac, then the
low-level vaddm simulates the high-level vaddm.
