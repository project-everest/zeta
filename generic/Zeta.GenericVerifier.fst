module Zeta.GenericVerifier

open Zeta.SeqIdx
open FStar.Classical

let hoist_ghost #_ #_ _ = admit ()

let hoist_ghost2 (#a:Type) (#b:a -> Type) (#c:(x:a -> b x -> Type)) (f:(x:a -> y:b x -> GTot (c x y))) = admit ()

let hoist_ghost2_apply #_ #_ #_ _ _ _ = admit ()

let hoist_ghost_restricted (#a:Type) (#b:a -> Type) (f:restricted_g_t a b)
  : GTot (g:restricted_t a b{forall x. f x == g x}) = admit ()

let not_contains_app_key (#vspec:_)
  (vtls: vspec.vtls_t{vspec.valid vtls})
  (s: vspec.slot_t)
  : GTot bool
  = not (contains_app_key vtls s)

let contains_only_app_keys_comp (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  : GTot (b:bool {b <==> contains_only_app_keys vtls ss})
  = not (exists_elems_with_prop_comp (hoist_ghost (not_contains_app_key vtls)) ss)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec search_level_2_aux (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls})
  (ss: S.seq vspec.slot_t{contains_only_app_keys vtls ss})
  (i1: SA.seq_index ss)
  (l: nat {l <= S.length ss})
  : GTot(o:option nat
    { None = o /\ (forall i2. i2 < l ==> i1 <> i2 ==> to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)) \/
      Some? o /\ (let i2 = Some?.v o in
                 i2 < l /\ i1 <> i2 /\
                 to_app_key vtls (S.index ss i1) = to_app_key vtls (S.index ss i2))})
    (decreases l)
  = if l = 0 then None
    else (
      let l' = l - 1 in
      let o = search_level_2_aux vtls ss i1 l' in
      if l' <> i1 && to_app_key vtls (S.index ss i1) = to_app_key vtls (S.index ss l') then
        Some l'
      else if Some? o then
        o
      else (
        let aux (i2:_)
          : Lemma (ensures (i2 < l ==> i1 <> i2 ==>
                            to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)))
          = if i2 < l' && i1 <> i2 then
            eliminate
            forall i2. i2 < l' ==> i1 <> i2 ==> to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)
            with i2
        in
        forall_intro aux;
        None
      )
    )

let search_level_2 (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls})
  (ss: S.seq vspec.slot_t{contains_only_app_keys vtls ss})
  (i1: SA.seq_index ss)
  : GTot (o:option nat
    { None = o /\ (forall i2. i1 <> i2 ==> to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)) \/
      Some? o /\ (let i2 = Some?.v o in
                 i1 <> i2 /\ i2 < S.length ss /\
                 to_app_key vtls (S.index ss i1) = to_app_key vtls (S.index ss i2))})
  = search_level_2_aux vtls ss i1 (S.length ss)

let rec search_level_1_aux (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls})
  (ss: S.seq vspec.slot_t{contains_only_app_keys vtls ss})
  (l: nat{l <= S.length ss})
  : GTot(o:option (nat * nat)
    { None = o /\ (forall i1 i2. i1 < l ==> i1 <> i2 ==>
                           to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)) \/
      Some? o /\ (let i1,i2 = Some?.v o in
                 i1 < l /\ i1 <> i2 /\ i2 < S.length ss /\
                 to_app_key vtls (S.index ss i1) = to_app_key vtls (S.index ss i2))
    })
    (decreases l)
  = if l = 0 then None
    else
      let i1 = l - 1 in
      let oi1 = search_level_2 vtls ss i1 in
      let ol' = search_level_1_aux vtls ss i1 in
      if Some? oi1 then
        let i2 = Some?.v oi1 in
        Some (i1,i2)
      else if Some? ol' then
        ol'
      else (
        let aux (j1:nat) (j2:_)
          : Lemma (ensures (j1 < l ==> j1 <> j2 ==>
                            to_app_key vtls (S.index ss j1) <> to_app_key vtls (S.index ss j2)))
          = if j1 < l && j1 <> j2 then
              if j1 = i1 then
                eliminate
                forall i2. i1 <> i2 ==> to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)
                with j2
              else
                eliminate
                forall i1 i2. i1 < l ==> i1 <> i2 ==>
                           to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)
                with j1 j2
        in
        forall_intro_2 aux;
        None
      )

let search_level_1 (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls})
  (ss: S.seq vspec.slot_t{contains_only_app_keys vtls ss})
  : GTot(o:option (nat * nat)
    { None = o /\ (forall i1 i2. i1 <> i2 ==>
                           to_app_key vtls (S.index ss i1) <> to_app_key vtls (S.index ss i2)) \/
      Some? o /\ (let i1,i2 = Some?.v o in
                 i1 <> i2 /\ i2 < S.length ss /\ i1 < S.length ss /\
                 to_app_key vtls (S.index ss i1) = to_app_key vtls (S.index ss i2))
    })
  = search_level_1_aux vtls ss (S.length ss)

let contains_distinct_app_keys_comp
  (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  : GTot (b:bool {b <==> contains_distinct_app_keys vtls ss})
  = contains_only_app_keys_comp vtls ss &&
    None = search_level_1 vtls ss
