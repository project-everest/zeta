module Zeta.SMap

open FStar.Classical

let rec monotonic_lower_bound_aux (#a:_) (#s1 #s2: seq a) (f: mono_smap s1 s2) (i j: seq_index s1)
  : Lemma (requires i >= j)
          (ensures (f i >= (f j) + i - j))
          (decreases i - j)
  = if i > j then (
      let i' = i - 1 in
      monotonic_lower_bound_aux f i' j;
      eliminate forall (i j: seq_index s1). i < j ==> f i < f j with i' i
    )

let monotonic_lower_bound (#a:_) (#s1 #s2: seq a) (f: mono_smap s1 s2) (i j: seq_index s1)
  : Lemma (ensures ((i >= j) ==> (f i >= (f j) + i - j)))
  = if i >= j then monotonic_lower_bound_aux f i j

let monotonic_implies_length (#a:_) (#s1 #s2: seq a) (f: mono_smap s1 s2)
  : Lemma (ensures (length s1 <= length s2))
  = if length s1 > 0 then
      let i = length s1 - 1 in
      monotonic_lower_bound f i 0

let monotonic_same_length_implies_identity (#a:_) (#s1 #s2: seq a) (f: mono_smap s1 s2) (i: seq_index s1)
  : Lemma (requires (length s1 = length s2))
          (ensures (f i = i))
  = monotonic_lower_bound f i 0;
    if f i > i then
      monotonic_lower_bound f (length s1 - 1) i

let monotonic_bijection_implies_equal (#a:_) (s1 s2: seq a)
  (f12: mono_smap s1 s2)
  (f21: mono_smap s2 s1)
  : Lemma (ensures (s1 == s2))
  = monotonic_implies_length f12;
    monotonic_implies_length f21;
    assert(length s1 = length s2);
    let aux (i:_)
      : Lemma (ensures (index s1 i == index s2 i))
      = monotonic_same_length_implies_identity f12 i
    in
    forall_intro aux;
    assert(equal s1 s2)
