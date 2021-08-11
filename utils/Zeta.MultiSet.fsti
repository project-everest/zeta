module Zeta.MultiSet

open Zeta.SeqAux

/// A multiset module
///
/// The type is indexed by a total order on the element type
///   There are other implementations possible that don't require a total order
///   For now, this works for our use case

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
  (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 == a2) /\  (* anti-symmetry *)
  (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)  /\  (* transitivity  *)
  (forall a1 a2. f a1 a2 \/ f a2 a1)                    (* totality      *)

type cmp (a:eqtype) = f:(a -> a -> bool){total_order a f}

/// The multiset type

val mset (a:eqtype) (f:cmp a) : Type0

/// Empty multiset

val empty (#a:eqtype) (#f:cmp a) : mset a f


/// Create a multiset that contains `m` copies of `x`

val create (#a:eqtype) (#f:cmp a) (x:a) (m:pos) : mset a f

/// Number of copies of `x` that `s` has

val mem (#a:eqtype) (#f:cmp a) (x:a) (s:mset a f) : nat

let contains (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a) : bool =
  mem x s > 0


/// Adding an element to a multiset

val add_elem (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a) : mset a f


/// Create a multiset from a sequence

val seq2mset (#a:eqtype) (#f:cmp a) (s:Seq.seq a) : mset a f


/// Union of two multisets

val union (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) : mset a f


/// Size of a multiset

val size (#a:eqtype) (#f:cmp a) (s:mset a f) : nat


/// If one multiset has size greater than another,
///   we can find an element whose cardinality in the first multiset is greater

val diff_elem (#a:eqtype) (#f:cmp a) (s1:mset a f) (s2:mset a f{size s1 > size s2})
  : (x:a{mem x s1 > mem x s2})


/// Index of an element in a sequence, that is contained in its corresponding multiset

val index_of_mselem (#a:eqtype) (#f:cmp a)
  (s:Seq.seq a)
  (x:a{seq2mset #a #f s `contains` x})
  : i:seq_index s{Seq.index s i == x}


/// Properties of multisets

/// Equality between two multisets

val equal (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) : Tot Type0

/// Two multisets are equal if forall `x:a`, they contain equal number of copies for `x`

val eq_intro (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires forall (x:a). mem x s1 = mem x s2)
      (ensures equal s1 s2)

/// Equality is reflexive

val eq_refl (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires s1 == s2)
      (ensures equal s1 s2)

/// Eliminate `equal` into propositional equality

val eq_elim (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma
      (requires equal s1 s2)
      (ensures s1 == s2)

/// If there is an element for which the number of copies in `s1` are not same as that
///   in `s2`, then `s1` and `s2` are not equal

val not_eq (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) (x:a)
  : Lemma
      (requires mem x s1 =!= mem x s2)
      (ensures (~ (s1 == s2)))


/// Equality of `Seq.count` and `mem` for `seq2mset`

val seq2mset_mem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma (mem x (seq2mset #_ #f s) == Seq.count x s)



/// An element of a sequence is contained in the corresponding multiset

val mset_contains_seq_element (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (i:seq_index s)
  : Lemma (seq2mset #a #f s `contains` Seq.index s i)


/// Commutation of `Seq.append` with `union`

val seq_append_mset (#a:eqtype) (#f:cmp a) (s1 s2:Seq.seq a)
  : Lemma (seq2mset #a #f (Seq.append s1 s2) == union (seq2mset #a #f s1) (seq2mset #a #f s2))

/// Commutation of `seq2mset` with `add_elem`

val seq2mset_add_elem (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (x:a)
  : Lemma (seq2mset #a #f (append1 s x) == add_elem (seq2mset #a #f s) x)


/// Relation between `seq2mset` for a sequence and its prefix

val seq_prefix_mset_mem (#a:eqtype) (#f:cmp a)
  (s:Seq.seq a)
  (s':Seq.seq a{is_prefix s s'})
  (x: a)
  : Lemma (mem x (seq2mset #a #f s') <= mem x (seq2mset #a #f s))


/// If an element occurs at least twice in a sequence,
///   then its cardinality in the corresponding multiset must be at least 2

val seq_mset_elem2 (#a:eqtype) (#f:cmp a) (s:Seq.seq a) (i1 i2:seq_index s)
  : Lemma
      (requires i1 =!= i2 /\ Seq.index s i1 == Seq.index s i2)
      (ensures mem (Seq.index s i1) (seq2mset #a #f s) >= 2)

/// Reasoning for `seq2mset` for sequences that are in bijection with each other


/// A mapping from one sequence to the other

type smap (#a:eqtype) (s1 s2:Seq.seq a) = f:(seq_index s1 -> seq_index s2){
  forall (i:seq_index s1). Seq.index s1 i == Seq.index s2 (f i)
}

/// Injectivity property on smaps

let into_smap (#a:eqtype) (s1 s2:Seq.seq a) = f:smap s1 s2{
  forall (i j: seq_index s1). (i =!= j) ==> f i =!= f j
}

/// If for two sequences, we can provide into_smaps in both the directions
///   then their corresponding multisets are equal

val bijection_seq_mset (#a:eqtype) (#f:cmp a)
  (s1 s2:Seq.seq a)
  (f12:into_smap s1 s2)
  (f21: into_smap s2 s1)
  : Lemma (seq2mset #a #f s1 == seq2mset #a #f s2)


/// Membership of an element in the union of two multisets

val union_mem (#a:eqtype) (#f:cmp a) (s1 s2:mset a f) (x:a)
  : Lemma (mem x (union s1 s2) == mem x s1 + mem x s2)


/// Union is commutative and associative

val union_comm (#a:eqtype) (#f:cmp a) (s1 s2:mset a f)
  : Lemma (union s1 s2 == union s2 s1)

val union_assoc (#a:eqtype) (#f:cmp a) (s1 s2 s3: mset a f)
  : Lemma (union (union s1 s2) s3 == union s1 (union s2 s3))


/// Adding an element increments the size by 1

val add_size (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
  : Lemma
      (ensures size (add_elem s x) == size s + 1)
      [SMTPat (add_elem s x)]

val length_size (#a:eqtype) (#f:cmp a) (s:Seq.seq a)
  : Lemma (Seq.length s = size (seq2mset #a #f s))


/// A multiset is a set when max cardinality of all elements is 1

let is_set (#a:eqtype) (#f:cmp a) (s:mset a f) = forall (x:a). mem x s <= 1

/// Adding an element increases the membership of that element by 1

val lemma_add_incr_mem (#a:eqtype) (#f:cmp a) (s:mset a f) (x:a)
  : Lemma (ensures mem x (add_elem s x) = 1 + mem x s)
