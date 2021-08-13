module Zeta.Generic.TSLog

module SA=Zeta.SeqAux

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor 2"

let lemma_prefix_clock_sorted #vspec (itsl: its_log vspec) (i:nat { i <= I.length itsl })
  : Lemma (requires (verifiable (prefix itsl i)))
          (ensures clock_sorted (prefix itsl i))
  = assert(clock_sorted itsl);
    let itsl' = prefix itsl i in
    let gl' = to_gvlog itsl' in
    let aux (t0 t1: seq_index itsl')
      : Lemma (requires t0 <= t1)
              (ensures clock itsl' t0 `ts_leq` clock itsl' t1)
              [SMTPat(clock itsl' t0 `ts_leq` clock itsl' t1)]
      = assert (clock itsl t0 `ts_leq` clock itsl t1);
        lemma_i2s_map_prefix itsl i t0;
        lemma_i2s_map_prefix itsl i t1;
        I.lemma_prefix_index itsl i t0;
        I.lemma_prefix_index itsl i t1;
        I.per_thread_prefix itsl i
    in
    ()

#pop-options

let lemma_prefix_verifiable #vspec (itsl: its_log vspec) (i:nat{i <= I.length itsl})
  : Lemma
    (ensures
      verifiable (I.prefix itsl i) /\
      clock_sorted (I.prefix itsl i))
  = assert (verifiable itsl);
    assert (clock_sorted itsl);
    let ss = to_gvlog itsl in
    let itsl' = I.prefix itsl i in
    let ss' = to_gvlog itsl' in
    assert (Seq.length ss = Seq.length ss');
    let aux (tid: SA.seq_index ss)
      : Lemma (T.verifiable (thread_log ss' tid))
              [SMTPat (thread_log ss' tid)]
      = let tl = thread_log ss tid in
        assert (T.verifiable tl);
        I.per_thread_prefix itsl i;
        let tl' = thread_log ss' tid in
        T.verifiable_implies_prefix_verifiable tl (Seq.length (snd tl'))
    in
    lemma_prefix_clock_sorted itsl i

noeq
type clock_gen #a (vl:sseq a) = {
   clock:(j:sseq_index vl ->  timestamp);
   monotone: (a:sseq_index vl -> b:sseq_index vl{fst a == fst b /\ snd a <= snd b} -> Lemma (clock a `ts_leq` clock b))
}

let clock_sorted_gen (#a:eqtype) (il:I.interleaving a) (c:clock_gen (I.s_seq il)) =
    forall (i j:I.seq_index il). {:pattern (i2s_map il i); (i2s_map il j)}
      i <= j ==>
        (let i' = i2s_map il i in
         let j' = i2s_map il j in
         c.clock i' `ts_leq` c.clock j')

#push-options "--fuel 0,0"

let sseq_same_shape #a #b (s0:sseq a) (s1:sseq b) =
  Seq.length s0 = Seq.length s1 /\
  (forall (i:SA.seq_index s0). Seq.length (Seq.index s0 i) = Seq.length (Seq.index s1 i))

let sseq_append #a (ss0:sseq a) (ss1:sseq a{Seq.length ss0 == Seq.length ss1})
  : sseq a
  = SA.mapi ss0 (fun i -> Seq.append (Seq.index ss0 i) (Seq.index ss1 i))

let ts_sorted_seq (s:Seq.seq ('a & timestamp)) =
  forall (i j:SA.seq_index s).
    i <= j ==>
    snd (Seq.index s i) `ts_leq` snd (Seq.index s j)

let ts_sseq 'a =
    s:sseq ('a & timestamp) {
      forall (i:SA.seq_index s). ts_sorted_seq (Seq.index s i)
    }

let is_min_clock_up_to (s:ts_sseq 'a) (i:nat{ i <= Seq.length s }) (min:sseq_index s)
  =  snd min == 0 /\
     (forall (j:sseq_index s).
       fst j < i ==> snd (indexss s min) `ts_leq` snd (indexss s j))

let min_clock_up_to (s:ts_sseq 'a) (i:nat{ i <= Seq.length s }) =
    min:sseq_index s { is_min_clock_up_to s i min }

let min_clock s = min_clock_up_to s (Seq.length s)

let rec pick_min (s:ts_sseq 'a)
                 (i:nat{i <= Seq.length s})
                 (min:min_clock_up_to s i)
  : Tot (min_clock s)
        (decreases (Seq.length s - i))
  = if i = Seq.length s then min
    else (
      if Seq.length (Seq.index s i) = 0
      then pick_min s (i + 1) min
      else (
        if snd (indexss s (i, 0)) `ts_leq`
           snd (indexss s min)
        then pick_min s (i + 1) (i,0)
        else (assert (snd (indexss s min) `ts_leq`
                      snd (indexss s (i, 0)));
              assert (forall (j:sseq_index s).
                        fst j = i /\
                        snd j >= 0 ==>
                        snd (indexss s min) `ts_leq`
                        snd (indexss s (i,0)) /\
                        snd (indexss s (i,0)) `ts_leq`
                        snd (indexss s j));
              pick_min s (i + 1) min
        )
      )
    )

let is_empty_sseq #a (s:sseq a) =
    forall (i:SA.seq_index s). Seq.index s i `Seq.equal` Seq.empty #a

let rec min_sseq_index(s:ts_sseq 'a)
  : Tot (o:option (sseq_index s) {
        match o with
        | None -> is_empty_sseq s
        | Some min -> is_min_clock_up_to s 0 min
        })
        (decreases (Seq.length s))
  = if Seq.length s = 0 then None
    else let prefix, last = Seq.un_snoc s in
         match min_sseq_index prefix with
         | None ->
           if Seq.length last = 0
           then None
           else (
             let min = (Seq.length s - 1, 0) in
             Some min
           )
         | Some i ->
           Some i

#push-options "--z3rlimit_factor 8"

let flat_length_single #a (s:seq a)
  : Lemma (flat_length (create 1 s) == Seq.length s)
  = assert (Seq.equal (create 1 s) (append1 empty s));
    lemma_flat_length_app1 empty s;
    lemma_flat_length_empty #a

let split_ts_sseq (s:ts_sseq 'a)
  : o:option (i:min_clock s &
              e:('a & timestamp){e == indexss s i} &
              s':ts_sseq 'a{
                Seq.length s = Seq.length s' /\
                s `Seq.equal` Seq.upd s (fst i)
                              (Seq.cons e (Seq.index s' (fst i))) /\
                flat_length s' < flat_length s
             }){
       None? o ==> is_empty_sseq s
    }
  = match min_sseq_index s with
    | None -> None
    | Some min ->
      let j = pick_min s 0 min in
      let e = Seq.head (Seq.index s (fst j)) in
      let tl_j = Seq.tail (Seq.index s (fst j)) in
      let s' = Seq.upd s (fst j) tl_j in
      assert (Seq.length (Seq.index s (fst j)) == Seq.length (Seq.index s' (fst j)) + 1);
      let s'_prefix, s'_suffix = Seq.split s' (fst j) in
      let s_prefix, s_suffix = Seq.split s (fst j) in
      assert (s_prefix == s'_prefix);
      let x', s'_suffix' = Seq.head s'_suffix, Seq.tail s'_suffix in
      let x, s_suffix' = Seq.head s_suffix, Seq.tail s_suffix in
      assert (s'_suffix' == s_suffix');
      assert (Seq.length x' < Seq.length x);
      lemma_flat_length_app s'_prefix s'_suffix;
      lemma_flat_length_app s_prefix s_suffix;
      assert (s'_suffix `Seq.equal` Seq.cons x' s'_suffix');
      assert (s_suffix `Seq.equal` Seq.cons x s_suffix');
      assert (s' `Seq.equal` (Seq.append s'_prefix s'_suffix));
      assert (s `Seq.equal` (Seq.append s_prefix s_suffix));
      // assert (flat_length s' == flat_length s'_prefix + flat_length s'_suffix);
      // assert (flat_length s == flat_length s_prefix + flat_length s_suffix);
      lemma_flat_length_app (create 1 x') s'_suffix';
      // assert (flat_length s'_suffix == flat_length (create 1 x') + flat_length s'_suffix');
      lemma_flat_length_app (create 1 x) s'_suffix';
      // assert (flat_length s_suffix == flat_length (create 1 x) + flat_length s'_suffix');
      flat_length_single x;
      flat_length_single x';
      assert (flat_length s' < flat_length s);
      Some (| j, e, s' |)
#pop-options

let ts_seq 'a = s:seq ('a & timestamp){ ts_sorted_seq s }

let get_min_clock (s:ts_sseq 'a { ~(is_empty_sseq s) })
  : ts:timestamp {
      forall (i:sseq_index s). ts `ts_leq` snd (indexss s i)
    }
  = let Some (| _, e, _|) = split_ts_sseq s in
    snd e

let clock_exceeds (s0:ts_seq 'a) (ts:timestamp) =
  forall (i:SA.seq_index s0). snd (Seq.index s0 i) `ts_leq` ts

let coerce_interleave (#a:eqtype) (s:seq a) (s0 s1:sseq a) (i:interleave s s0 { Seq.equal s0 s1 })
  : interleave s s1
  = i

#push-options "--z3rlimit_factor 6"
let rec interleave_ts_sseq
         (#a:eqtype)
         (s0:ts_seq a)
         (ss0:ts_sseq a)
         (ss1:ts_sseq a{
           (Seq.length ss0 == Seq.length ss1) /\
           (is_empty_sseq ss1 \/
            (clock_exceeds s0 (get_min_clock ss1) /\
             (forall (i:SA.seq_index ss0).
               clock_exceeds (Seq.index ss0 i) (get_min_clock ss1))))
          })
         (prefix:interleave s0 ss0)
   : Tot (s:ts_seq a &
          interleave s
                     (ss0 `sseq_append` ss1))
         (decreases (flat_length ss1))
   = match split_ts_sseq ss1 with
     | None ->
       assert (is_empty_sseq ss1);
       assert (forall (i:SA.seq_index ss0).
               Seq.equal (Seq.index ss0 i)
                         (Seq.append (Seq.index ss0 i) empty));
       assert (Seq.equal ss0 (ss0 `sseq_append` ss1));
       (| s0, prefix |)

     | Some (| i, e, ss1' |) ->
       let s0' : ts_seq a = append1 s0 e in
       let prefix' : interleave (append1 s0 e) (sseq_extend ss0 e (fst i))
         = I.IntExtend s0 ss0 prefix e (fst i)
       in
       let ss0' = sseq_extend ss0 e (fst i) in
       let aux (j:SA.seq_index ss0)
         : Lemma
           (ensures (Seq.index (sseq_append ss0' ss1') j `Seq.equal` Seq.index (sseq_append ss0 ss1) j))
           [SMTPat (Seq.index (sseq_append ss0' ss1') j)]
         = let v = sseq_append ss0 ss1 in
           let v' = sseq_append ss0' ss1' in
           if fst i <> j
           then ()
           else (
             assert (Seq.index v j == Seq.append (Seq.index ss0 j) (Seq.index ss1 j));
             assert (Seq.index ss1' j == Seq.tail (Seq.index ss1 j));
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) (Seq.head (Seq.index ss1 j)))
           )
       in
       assert ((sseq_append ss0' ss1') `Seq.equal` (sseq_append ss0 ss1));
       let aux (j:SA.seq_index ss0')
         : Lemma (ensures ts_sorted_seq (Seq.index ss0' j))
                 [SMTPat (Seq.index ss0' j)]
         = if fst i <> j
           then ()
           else (
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) (Seq.head (Seq.index ss1 j)));
             assert (Seq.head (Seq.index ss1 j) == e);
             assert (clock_exceeds (Seq.index ss0' j) (snd e))
           )
       in
       assert (forall (i:SA.seq_index ss0'). ts_sorted_seq (Seq.index ss0' i));
       let aux ()
         : Lemma (requires ~(is_empty_sseq ss1'))
                 (ensures (clock_exceeds s0' (get_min_clock ss1')))
                 [SMTPat()]
         = assert (snd e `ts_leq` (get_min_clock ss1'));
           assert (s0' == Seq.snoc s0 e);
           assert (clock_exceeds s0 (snd e));
           assert (forall (i:SA.seq_index s0').
                     snd (Seq.index s0' i) `ts_leq` (snd e) /\
                     snd e `ts_leq` (get_min_clock ss1'))
       in
       let aux (j:SA.seq_index ss0')
         : Lemma (requires ~(is_empty_sseq ss1'))
                 (ensures (clock_exceeds (Seq.index ss0' j) (get_min_clock ss1')))
                 [SMTPat()]
         = assert (clock_exceeds (Seq.index ss0 j) (get_min_clock ss1));
           assert (clock_exceeds (Seq.index ss0 j) (snd e));
           assert (snd e `ts_leq` get_min_clock ss1');
           if fst i <> j
           then (
             assert (Seq.index ss0 j == Seq.index ss0' j)
           )
           else (
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) e);
             let ss = Seq.index ss0' j in
             assert (forall (i:SA.seq_index ss).
                     snd (Seq.index ss i) `ts_leq` (snd e) /\
                     snd e `ts_leq` (get_min_clock ss1'));
             ()
           )
       in
       let (| s, p |) = interleave_ts_sseq s0' ss0' ss1' prefix' in
       (| s, coerce_interleave s _ _ p |)
#pop-options

let create_tsseq_interleaving (#a:eqtype) (ss:ts_sseq a)
  : (s:ts_seq a & interleave s ss)
  = let (| s, i |) = interleave_ts_sseq empty (create (Seq.length ss) empty) ss (interleave_empty_n _) in
    assert (forall (i:SA.seq_index ss).
           Seq.index ((create (Seq.length ss) empty) `sseq_append` ss) i
           `Seq.equal`
           Seq.index ss i);
    assert (((create (Seq.length ss) empty) `sseq_append` ss) `Seq.equal` ss);
    (| s, coerce_interleave _ _ _ i |)

let with_clock_i_gen (vl:sseq 'a)
                     (c:clock_gen vl)
                     (i:SA.seq_index vl)
  : s:ts_seq 'a {
      Seq.length s = Seq.length (Seq.index vl i) /\
      (forall (j:SA.seq_index s). (indexss vl (i,j), c.clock (i,j)) == Seq.index s j)
    }
  = let vl_i = Seq.index vl i in
    let s = mapi vl_i (fun j -> Seq.index vl_i j, c.clock (i, j)) in
    let aux (a b:SA.seq_index s)
      : Lemma
        (requires a <= b)
        (ensures snd (Seq.index s a) `ts_leq` snd (Seq.index s b))
        [SMTPat (Seq.index s a);
         SMTPat (Seq.index s b)]
      = c.monotone (i, a) (i, b)
    in
    s

let mk_clock_gen #vspec (vl:G.verifiable_log vspec)
  : clock_gen vl
  = let lem (a:sseq_index vl) (b:sseq_index vl{fst a == fst b /\ snd a <= snd b})
      : Lemma (G.clock vl a `ts_leq` G.clock vl b)
      =      T.lemma_clock_monotonic (G.thread_log vl (fst a)) (snd a) (snd b)
    in
    let c = {
      clock = G.clock vl;
      monotone = lem;
    } in
    c

let map_tsseq (f:('a & timestamp) -> 'b) (x:ts_sseq 'a)
  : sseq 'b
  = map (map f) x

let ts_seq_of_g_vlog (vl:sseq 'a) (c:clock_gen vl)
  : s:ts_sseq 'a {
      sseq_same_shape vl s /\
      (forall (i:sseq_index s).
         indexss s i == (indexss vl i, c.clock i))
    }
  = mapi vl (with_clock_i_gen vl c)

let g_vlog_of_ts_sseq (x:ts_sseq 'a)
  : sseq 'a
  = map_tsseq fst x

let inverse_g_vlog_ts_seq (vl:sseq 'a) (c:clock_gen vl)
  : Lemma (g_vlog_of_ts_sseq (ts_seq_of_g_vlog vl c) == vl)
  = let ts = ts_seq_of_g_vlog vl c in
    let vl' = g_vlog_of_ts_sseq ts in
    assert (Seq.length ts == Seq.length vl');
    let aux (i:SA.seq_index ts)
      : Lemma (ensures Seq.index vl' i `Seq.equal` Seq.index vl i)
              [SMTPat (Seq.index vl i)]
      = ()
    in
    assert (Seq.equal vl' vl)

let create_gen (#a:eqtype) (vl: sseq a) (c:clock_gen vl)
  : (itsl:I.interleaving a{I.s_seq itsl == vl /\ clock_sorted_gen itsl c})
  = let ts = ts_seq_of_g_vlog vl c in
    let (| s, tsi |) = create_tsseq_interleaving ts in
    inverse_g_vlog_ts_seq vl c;
    let il = IL _ vl (map_interleave fst _ _ tsi) in
    assert (I.s_seq il == vl);
    let aux (i j: I.seq_index il)
      : Lemma (requires i <= j)
              (ensures (
                let i' = i2s_map il i in
                let j' = i2s_map il j in
                c.clock i' `ts_leq` c.clock j'))
              [SMTPat ()]
      = let i' = i2s_map il i in
        let j' = i2s_map il j in
        map_interleave_i2s fst (IL _ _ tsi) i;
        map_interleave_i2s fst (IL _ _ tsi) j;
        assert (c.clock i' == snd (indexss ts i'));
        assert (c.clock j' == snd (indexss ts j'));
        lemma_i2s_s2i il i;
        lemma_i2s_s2i il j;
        assert (indexss ts i' == Seq.index s (s2i_map il i'));
        assert (indexss ts j' == Seq.index s (s2i_map il j'));
        assert (indexss ts i' == Seq.index s i);
        assert (indexss ts j' == Seq.index s j);
        assert (c.clock i' `ts_leq` c.clock j')
    in
    assert (clock_sorted_gen il c);
    il

let create #vspec (gl:G.verifiable_log vspec)
  = create_gen gl (mk_clock_gen gl)

#pop-options

