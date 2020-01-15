module Veritas.SubSeq

open FStar.Seq

(* Legitimate values of an index of a sequence *)
type seq_index (#a:Type) (s:seq a) = i:nat{i < length s}

let prefix (#a:Type) (s:seq a) (i:nat{i <= length s}) = slice s 0 i

let rec filter (#a:Type) (s:seq a) (f:a -> bool): Tot (seq a)  
  (decreases (length s)) = 
  let n = length s in
  if n = 0 then empty
  else 
    let e = index s (n - 1) in 
    if f e then 
      append (filter (prefix s (n - 1)) f) (create 1 e)
    else 
      filter (prefix s (n - 1)) f

let rec filter_len_monotonic (#a:Type) (s:seq a) (f:a -> bool) (i:nat{i <= length s}):
  Lemma (requires (True))
        (ensures (length (filter s f) >= length (filter (prefix s i) f)))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else if i  = n then () // s == prefix s i
  else (
    lemma_len_slice s 0 (n - 1);
    filter_len_monotonic (prefix s (n - 1)) f i
  )

let rank (#a:Type) (s:seq a) (f:a -> bool) (i:nat{i <= length s})
  = length (filter (prefix s i) f)
        
let filter_index_map (#a:Type) (s:seq a) (f:a -> bool) (i:seq_index s{f (index s i)}):
  Tot (seq_index (filter s f)) = 
  filter_len_monotonic s f (i+1);
  lemma_len_append (filter (prefix s i) f) (create 1 (index s i));
  rank s f i

let rec filter_index_map_correct (#a:eqtype) (s:seq a) (f:a -> bool) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (index s i = index (filter s f) (filter_index_map s f i)))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else filter_index_map_correct (prefix s (n - 1)) f i

let filter_index_map_monotonic (#a:eqtype) (s:seq a) (f:a -> bool) 
  (i:seq_index s) (j:seq_index s{j > i}):
  Lemma (requires (f (index s i) && f (index s j)))
        (ensures (filter_index_map s f i < filter_index_map s f j)) =
  filter_len_monotonic (prefix s j) f (i + 1)

let rank_increases_by_atmost_one (#a:eqtype) (s:seq a) (f:a -> bool)
  (i:seq_index s):
  Lemma (requires (True))
        (ensures (f (index s i) && (rank s f i) + 1 = rank s f (i + 1) || 
                  not (f (index s i)) && rank s f i = rank s f (i + 1))) = ()

let rec rank_search (#a:eqtype) (s:seq a) (f:a -> bool) 
                (r:seq_index (filter s f)) 
                (i:nat{i <= length s && rank s f i > r})
  : Tot (j:seq_index s{rank s f j = r && f (index s j)})
    (decreases i) = 
  assert (i > 0);
  if rank s f (i - 1) = r then (i - 1)
  else (
    rank_increases_by_atmost_one s f (i - 1);
    rank_search s f r (i - 1)
  )

let filter_index_inv_map (#a:eqtype) (s:seq a) (f:a -> bool) (r:seq_index (filter s f))
  : Tot (j:seq_index s{rank s f j = r && f (index s j)}) = 
  rank_search s f r (length s)

let last_index (#a:eqtype) (s:seq a) (f:a -> bool):
  Tot (option (seq_index s)) = 
  let fs = filter s f in
  if length fs = 0 then None
  else Some (filter_index_inv_map s f ((length fs) - 1))

let last_index_correct1 (#a:eqtype) (s:seq a) (f:a -> bool):
  Lemma (requires (Some? (last_index s f)))
        (ensures (f (index s (Some?.v (last_index s f))))) = ()
                   
let last_index_correct2 (#a:eqtype) (s:seq a) (f:a -> bool) (i:seq_index s):
  Lemma (requires (Some? (last_index s f) && 
                   i > Some?.v (last_index s f)))
        (ensures (not (f (index s i)))) =
  let j = Some?.v (last_index s f) in 
  if f (index s i) then 
    filter_index_map_monotonic s f j i  
  else ()

let rec exists_implies_last_index (#a:eqtype) (s:seq a) (f:a -> bool) (i:seq_index s):
  Lemma (requires (f (index s i)))
        (ensures (Some? (last_index s f)))
        (decreases (length s)) = 
  let n = length s in
  if n = 0 then ()
  else if i = n - 1 then ()
  else exists_implies_last_index (slice s 0 (n - 1)) f i    

let last_index_prefix (#a:eqtype) (s:seq a{length s > 0}) (f:a -> bool):
  Lemma (requires (Some? (last_index s f) && not (f (index s (length s - 1)))))
        (ensures (Some?.v (last_index s f) = Some?.v (last_index (prefix s (length s - 1)) f))) = 
  let n = length s in
  let s' = prefix s (n - 1) in
  let li = Some?.v (last_index s f) in
  let li' = Some?.v (last_index s' f) in
  if li < li' then filter_index_map_monotonic s f li li'
  else if li' < li then filter_index_map_monotonic s f li' li
  else ()
