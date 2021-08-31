module Zeta.FilterMap

let rec filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  : Tot (seq b)
    (decreases length s)
  = let n = length s in
    if n = 0
    then empty #b
    else
      let s' = prefix s (n - 1) in
      let ms' = filter_map fm s' in
      if fm.f (telem s)
      then append1 ms' (fm.m s (n - 1))
      else ms'

let rec filter_map_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : Tot(j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i})
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if i = n
    then length ms'
    else filter_map_map fm s' i

let rec filter_map_invmap (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (j: seq_index (filter_map fm s))
  : Tot(i:(seq_index s){ fm.f (index s i) /\ filter_map_map fm s i = j })
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if j = length ms'
    then n
    else filter_map_invmap fm s' j

let rec lemma_filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else lemma_filter_map fm s' i

let lemma_filter_map_extend_sat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ fm.f (telem s)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ not (fm.f (telem s))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
  = ()

let lemma_ss_prefix_property
  (#a:_)
  (#b:eqtype)
  (f: a -> bool)
  (m: (nat -> s:seq a -> i:seq_index s{f (index s i)} -> b))
  (t: nat)
  : Lemma (ensures (prefix_property f (m t)))
  = let m' = m t in
    let aux (s: seq a)
      : Lemma (ensures (forall (i:nat).
                        forall (j:nat).
                        j <= length s ==>
                        i < j ==>
                        f (index s i) ==>
                        m' s i = m' (prefix s j) i))
      = let aux2 (i:nat)
          : Lemma (ensures (forall (j:nat).
                        j <= length s ==>
                        i < j ==>
                        f (index s i) ==>
                        m' s i = m' (prefix s j) i))
            = let aux3 (j:nat)
                : Lemma (ensures (
                        j <= length s ==>
                        i < j ==>
                        f (index s i) ==>
                        m' s i = m' (prefix s j) i))
                = if j > length s then ()
                  else if i >= j then ()
                  else if not (f (index s i)) then ()
                  else (
                    assume(m t s i = m t (prefix s j) i)
                  )
            in
            FStar.Classical.forall_intro aux3
        in
        FStar.Classical.forall_intro aux2
    in
    FStar.Classical.forall_intro aux


let rec ssfilter_map (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  : Tot (s':sseq b {length s' = length s})
    (decreases (length s))
  = let n = length s in
    if n = 0 then empty #(seq b)
    else
      let fmss' = ssfilter_map fm (prefix s (n-1)) in
      admit()
