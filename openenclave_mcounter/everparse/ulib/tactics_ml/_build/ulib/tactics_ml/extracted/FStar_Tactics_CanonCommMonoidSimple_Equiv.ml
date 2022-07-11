open Prims
type atom = Prims.int
type exp =
  | Unit 
  | Mult of exp * exp 
  | Atom of atom 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let (uu___is_Atom : exp -> Prims.bool) =
  fun projectee -> match projectee with | Atom _0 -> true | uu___ -> false
let (__proj__Atom__item___0 : exp -> atom) =
  fun projectee -> match projectee with | Atom _0 -> _0
let rec (exp_to_string : exp -> Prims.string) =
  fun e ->
    match e with
    | Unit -> "Unit"
    | Atom x -> Prims.strcat "Atom " (Prims.string_of_int x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type 'a amap = ((atom * 'a) Prims.list * 'a)
let const : 'a . 'a -> 'a amap = fun xa -> ([], xa)
let select : 'a . atom -> 'a amap -> 'a =
  fun x ->
    fun am ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst am) with
      | FStar_Pervasives_Native.Some a1 -> a1
      | uu___ -> FStar_Pervasives_Native.snd am
let update : 'a . atom -> 'a -> 'a amap -> 'a amap =
  fun x ->
    fun xa ->
      fun am ->
        (((x, xa) :: (FStar_Pervasives_Native.fst am)),
          (FStar_Pervasives_Native.snd am))
let rec mdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, unit) FStar_Algebra_CommMonoid_Equiv.cm -> 'a amap -> exp -> 'a
  =
  fun eq ->
    fun m ->
      fun am ->
        fun e ->
          match e with
          | Unit ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
          | Atom x -> select x am
          | Mult (e1, e2) ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
                (mdenote eq m am e1) (mdenote eq m am e2)
let rec xsdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'a amap -> atom Prims.list -> 'a
  =
  fun eq ->
    fun m ->
      fun am ->
        fun xs ->
          match xs with
          | [] -> FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
          | x::[] -> select x am
          | x::xs' ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
                (select x am) (xsdenote eq m am xs')
let rec (flatten : exp -> atom Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Atom x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)


type permute = atom Prims.list -> atom Prims.list
type 'p permute_correct = unit
type 'n swap = Prims.nat
let rec apply_swap_aux :
  'a . Prims.nat -> 'a Prims.list -> unit swap -> 'a Prims.list =
  fun n ->
    fun xs ->
      fun s ->
        match xs with
        | [] -> xs
        | uu___::[] -> xs
        | x1::x2::xs' ->
            if n = s
            then x2 :: x1 :: xs'
            else x1 :: (apply_swap_aux (n + Prims.int_one) (x2 :: xs') s)
let apply_swap : 'a . unit -> 'a Prims.list -> unit swap -> 'a Prims.list =
  fun uu___ -> apply_swap_aux Prims.int_zero


let rec apply_swaps :
  'a . 'a Prims.list -> unit swap Prims.list -> 'a Prims.list =
  fun xs ->
    fun ss ->
      match ss with
      | [] -> xs
      | s::ss' -> apply_swaps ((apply_swap ()) xs s) ss'

type 'p permute_via_swaps = unit


let (sort : permute) =
  FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))



let (canon : exp -> atom Prims.list) = fun e -> sort (flatten e)



let rec (where_aux :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        Prims.nat FStar_Pervasives_Native.option)
  =
  fun n ->
    fun x ->
      fun xs ->
        match xs with
        | [] -> FStar_Pervasives_Native.None
        | x'::xs' ->
            if FStar_Reflection_Builtins.term_eq x x'
            then FStar_Pervasives_Native.Some n
            else where_aux (n + Prims.int_one) x xs'
let (where :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      Prims.nat FStar_Pervasives_Native.option)
  = where_aux Prims.int_zero
let (fatom :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      FStar_Reflection_Types.term amap ->
        FStar_Tactics_Types.proofstate ->
          (exp * FStar_Reflection_Types.term Prims.list *
            FStar_Reflection_Types.term amap) FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ts ->
      fun am ->
        match where t ts with
        | FStar_Pervasives_Native.Some v ->
            (fun s -> FStar_Tactics_Result.Success (((Atom v), ts, am), s))
        | FStar_Pervasives_Native.None ->
            (fun ps ->
               match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (305))
                                      (Prims.of_int (17))
                                      (Prims.of_int (305))
                                      (Prims.of_int (26))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (306)) (Prims.of_int (4))
                                (Prims.of_int (307)) (Prims.of_int (47)))))
               with
               | true ->
                   (match (FStar_Tactics_Derived.norm_term
                             [FStar_Pervasives.iota; FStar_Pervasives.zeta] t)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (26))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                              (Prims.of_int (306))
                                              (Prims.of_int (4))
                                              (Prims.of_int (307))
                                              (Prims.of_int (47))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                        (Prims.of_int (306))
                                        (Prims.of_int (12))
                                        (Prims.of_int (306))
                                        (Prims.of_int (36))))))
                    with
                    | FStar_Tactics_Result.Success (a, ps') ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                          (Prims.of_int (307))
                                          (Prims.of_int (4))
                                          (Prims.of_int (307))
                                          (Prims.of_int (47)))))
                         with
                         | true ->
                             FStar_Tactics_Result.Success
                               (((Atom (FStar_List_Tot_Base.length ts)),
                                  (FStar_List_Tot_Base.op_At ts [a]),
                                  (update (FStar_List_Tot_Base.length ts) a
                                     am)),
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (307))
                                             (Prims.of_int (4))
                                             (Prims.of_int (307))
                                             (Prims.of_int (47))))))))
                    | FStar_Tactics_Result.Failed (e, ps') ->
                        FStar_Tactics_Result.Failed (e, ps')))
let rec (reification_aux :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term amap ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Tactics_Types.proofstate ->
              (exp * FStar_Reflection_Types.term Prims.list *
                FStar_Reflection_Types.term amap)
                FStar_Tactics_Result.__result)
  =
  fun ts ->
    fun am ->
      fun mult ->
        fun unit ->
          fun t ->
            fun ps ->
              match FStar_Tactics_Types.tracepoint
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (312)) (Prims.of_int (15))
                                     (Prims.of_int (312)) (Prims.of_int (32))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                               (Prims.of_int (312)) (Prims.of_int (2))
                               (Prims.of_int (323)) (Prims.of_int (22)))))
              with
              | true ->
                  ((match FStar_Reflection_Derived_Lemmas.collect_app_ref t
                    with
                    | (hd, tl) ->
                        (fun ps1 ->
                           match match (FStar_Tactics_Builtins.inspect hd)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                           (Prims.of_int (313))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (313))
                                                           (Prims.of_int (33))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                     (Prims.of_int (313))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (313))
                                                     (Prims.of_int (18))))))
                                 with
                                 | FStar_Tactics_Result.Success (a, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (33)))))
                                      with
                                      | true ->
                                          FStar_Tactics_Result.Success
                                            ((a,
                                               (FStar_List_Tot_Base.list_unref
                                                  tl)),
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (313))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (313))
                                                          (Prims.of_int (33))))))))
                                 | FStar_Tactics_Result.Failed (e, ps') ->
                                     FStar_Tactics_Result.Failed (e, ps')
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                 (Prims.of_int (313))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (323))
                                                 (Prims.of_int (22)))))
                                with
                                | true ->
                                    ((match a with
                                      | (FStar_Reflection_Data.Tv_FVar fv,
                                         (t1,
                                          FStar_Reflection_Data.Q_Explicit)::
                                         (t2,
                                          FStar_Reflection_Data.Q_Explicit)::[])
                                          ->
                                          (fun ps2 ->
                                             match match (FStar_Tactics_Builtins.pack
                                                            (FStar_Reflection_Data.Tv_FVar
                                                               fv))
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (39))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (34))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a1, ps'1) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (39)))))
                                                        with
                                                        | true ->
                                                            FStar_Tactics_Result.Success
                                                              ((FStar_Reflection_Builtins.term_eq
                                                                  a1 mult),
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (39))))))))
                                                   | FStar_Tactics_Result.Failed
                                                       (e, ps'1) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'1)
                                             with
                                             | FStar_Tactics_Result.Success
                                                 (a1, ps'1) ->
                                                 (match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                   (Prims.of_int (315))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (319))
                                                                   (Prims.of_int (22)))))
                                                  with
                                                  | true ->
                                                      (if a1
                                                       then
                                                         (fun ps3 ->
                                                            match (reification_aux
                                                                    ts am
                                                                    mult unit
                                                                    t1)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (63))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a2, ps'2) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (31)))))
                                                                 with
                                                                 | true ->
                                                                    ((match a2
                                                                    with
                                                                    | (e1,
                                                                    ts1, am1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    ts1 am1
                                                                    mult unit
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (63))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a3
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    am2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, am2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (30))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (31)))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps'2) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'2))
                                                       else fatom t ts am)
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (22)))))))
                                             | FStar_Tactics_Result.Failed
                                                 (e, ps'1) ->
                                                 FStar_Tactics_Result.Failed
                                                   (e, ps'1))
                                      | (uu___, uu___1) ->
                                          if
                                            FStar_Reflection_Builtins.term_eq
                                              t unit
                                          then
                                            (fun s ->
                                               FStar_Tactics_Result.Success
                                                 ((Unit, ts, am), s))
                                          else fatom t ts am))
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                  (Prims.of_int (313))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (323))
                                                  (Prims.of_int (22)))))))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (312))
                                      (Prims.of_int (15))
                                      (Prims.of_int (312))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (312)) (Prims.of_int (2))
                                (Prims.of_int (323)) (Prims.of_int (22))))))
let (reification :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        FStar_Reflection_Types.term amap ->
          FStar_Reflection_Types.term ->
            FStar_Tactics_Types.proofstate ->
              (exp * FStar_Reflection_Types.term Prims.list *
                FStar_Reflection_Types.term amap)
                FStar_Tactics_Result.__result)
  =
  fun eq ->
    fun m ->
      fun ts ->
        fun am ->
          fun t ->
            fun ps ->
              match (FStar_Tactics_Derived.norm_term
                       [FStar_Pervasives.iota;
                       FStar_Pervasives.zeta;
                       FStar_Pervasives.delta]
                       (FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_App
                             ((FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Algebra";
                                       "CommMonoid";
                                       "Equiv";
                                       "__proj__CM__item__mult"]))),
                               (m, FStar_Reflection_Data.Q_Explicit)))))
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                  (Prims.of_int (327)) (Prims.of_int (13))
                                  (Prims.of_int (327)) (Prims.of_int (60))))))
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                    (Prims.of_int (328)) (Prims.of_int (2))
                                    (Prims.of_int (330)) (Prims.of_int (35)))))
                   with
                   | true ->
                       (match (FStar_Tactics_Derived.norm_term
                                 [FStar_Pervasives.iota;
                                 FStar_Pervasives.zeta;
                                 FStar_Pervasives.delta]
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_App
                                       ((FStar_Reflection_Builtins.pack_ln
                                           (FStar_Reflection_Data.Tv_FVar
                                              (FStar_Reflection_Builtins.pack_fv
                                                 ["FStar";
                                                 "Algebra";
                                                 "CommMonoid";
                                                 "Equiv";
                                                 "__proj__CM__item__unit"]))),
                                         (m,
                                           FStar_Reflection_Data.Q_Explicit)))))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                  (Prims.of_int (328))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (330))
                                                  (Prims.of_int (35))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                            (Prims.of_int (328))
                                            (Prims.of_int (13))
                                            (Prims.of_int (328))
                                            (Prims.of_int (60))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                              (Prims.of_int (329))
                                              (Prims.of_int (2))
                                              (Prims.of_int (330))
                                              (Prims.of_int (35)))))
                             with
                             | true ->
                                 (match (FStar_Tactics_Derived.norm_term
                                           [FStar_Pervasives.iota;
                                           FStar_Pervasives.zeta] t)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                            (Prims.of_int (329))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (330))
                                                            (Prims.of_int (35))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                      (Prims.of_int (329))
                                                      (Prims.of_int (13))
                                                      (Prims.of_int (329))
                                                      (Prims.of_int (37))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                        (Prims.of_int (330))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (330))
                                                        (Prims.of_int (35)))))
                                       with
                                       | true ->
                                           (reification_aux ts am a a1 a2)
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                         (Prims.of_int (330))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (330))
                                                         (Prims.of_int (35)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
let rec (repeat_cong_right_identity :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun eq ->
    fun m ->
      FStar_Tactics_Derived.or_else
        (fun uu___ ->
           FStar_Tactics_Derived.apply_lemma
             (FStar_Reflection_Builtins.pack_ln
                (FStar_Reflection_Data.Tv_FVar
                   (FStar_Reflection_Builtins.pack_fv
                      ["FStar";
                      "Algebra";
                      "CommMonoid";
                      "Equiv";
                      "right_identity"]))))
        (fun uu___ ->
           fun ps ->
             match (FStar_Tactics_Derived.apply_lemma
                      (FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_App
                            ((FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Algebra";
                                      "CommMonoid";
                                      "Equiv";
                                      "__proj__CM__item__congruence"]))),
                              (m, FStar_Reflection_Data.Q_Explicit)))))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                 (Prims.of_int (334)) (Prims.of_int (20))
                                 (Prims.of_int (334)) (Prims.of_int (55))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                   (Prims.of_int (335)) (Prims.of_int (20))
                                   (Prims.of_int (337)) (Prims.of_int (51)))))
                  with
                  | true ->
                      (match (FStar_Tactics_Logic.split ())
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                 (Prims.of_int (335))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (337))
                                                 (Prims.of_int (51))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                           (Prims.of_int (335))
                                           (Prims.of_int (20))
                                           (Prims.of_int (335))
                                           (Prims.of_int (28))))))
                       with
                       | FStar_Tactics_Result.Success (a1, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (336))
                                             (Prims.of_int (20))
                                             (Prims.of_int (337))
                                             (Prims.of_int (51)))))
                            with
                            | true ->
                                (match (FStar_Tactics_Derived.apply_lemma
                                          (FStar_Reflection_Builtins.pack_ln
                                             (FStar_Reflection_Data.Tv_App
                                                ((FStar_Reflection_Builtins.pack_ln
                                                    (FStar_Reflection_Data.Tv_FVar
                                                       (FStar_Reflection_Builtins.pack_fv
                                                          ["FStar";
                                                          "Algebra";
                                                          "CommMonoid";
                                                          "Equiv";
                                                          "__proj__EQ__item__reflexivity"]))),
                                                  (eq,
                                                    FStar_Reflection_Data.Q_Explicit)))))
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                           (Prims.of_int (336))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (337))
                                                           (Prims.of_int (51))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                     (Prims.of_int (336))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (336))
                                                     (Prims.of_int (57))))))
                                 with
                                 | FStar_Tactics_Result.Success (a2, ps'2) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'2
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                       (Prims.of_int (337))
                                                       (Prims.of_int (20))
                                                       (Prims.of_int (337))
                                                       (Prims.of_int (51)))))
                                      with
                                      | true ->
                                          (repeat_cong_right_identity eq m)
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                        (Prims.of_int (337))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (337))
                                                        (Prims.of_int (51)))))))
                                 | FStar_Tactics_Result.Failed (e, ps'2) ->
                                     FStar_Tactics_Result.Failed (e, ps'2)))
                       | FStar_Tactics_Result.Failed (e, ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec (convert_map :
  (atom * FStar_Reflection_Types.term) Prims.list ->
    FStar_Reflection_Types.term)
  =
  fun m ->
    match m with
    | [] ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv ["Prims"; "Nil"]))
    | (a, t)::ps ->
        let a1 =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int a)) in
        let uu___ = convert_map ps in
        let uu___1 = t in
        let uu___2 = a1 in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["Prims"; "Cons"]))),
                      ((FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_App
                             ((FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_App
                                    ((FStar_Reflection_Builtins.pack_ln
                                        (FStar_Reflection_Data.Tv_FVar
                                           (FStar_Reflection_Builtins.pack_fv
                                              ["FStar";
                                              "Pervasives";
                                              "Native";
                                              "Mktuple2"]))),
                                      (uu___2,
                                        FStar_Reflection_Data.Q_Explicit)))),
                               (uu___1, FStar_Reflection_Data.Q_Explicit)))),
                        FStar_Reflection_Data.Q_Explicit)))),
               (uu___, FStar_Reflection_Data.Q_Explicit)))
let (convert_am :
  FStar_Reflection_Types.term amap -> FStar_Reflection_Types.term) =
  fun am ->
    let uu___ = am in
    match uu___ with
    | (map, def) ->
        let uu___1 = def in
        let uu___2 = convert_map map in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                      (uu___2, FStar_Reflection_Data.Q_Explicit)))),
               (uu___1, FStar_Reflection_Data.Q_Explicit)))
let rec (quote_exp : exp -> FStar_Reflection_Types.term) =
  fun e ->
    match e with
    | Unit ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar";
                "Tactics";
                "CanonCommMonoidSimple";
                "Equiv";
                "Unit"]))
    | Mult (e1, e2) ->
        let uu___ = quote_exp e2 in
        let uu___1 = quote_exp e1 in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "CanonCommMonoidSimple";
                              "Equiv";
                              "Mult"]))),
                      (uu___1, FStar_Reflection_Data.Q_Explicit)))),
               (uu___, FStar_Reflection_Data.Q_Explicit)))
    | Atom n ->
        let nt =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int n)) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["FStar";
                       "Tactics";
                       "CanonCommMonoidSimple";
                       "Equiv";
                       "Atom"]))), (nt, FStar_Reflection_Data.Q_Explicit)))
let (canon_lhs_rhs :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Tactics_Types.proofstate ->
            unit FStar_Tactics_Result.__result)
  =
  fun eq ->
    fun m ->
      fun lhs ->
        fun rhs ->
          fun ps ->
            match (FStar_Tactics_Derived.norm_term
                     [FStar_Pervasives.iota;
                     FStar_Pervasives.zeta;
                     FStar_Pervasives.delta]
                     (FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_App
                           ((FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Algebra";
                                     "CommMonoid";
                                     "Equiv";
                                     "__proj__CM__item__unit"]))),
                             (m, FStar_Reflection_Data.Q_Explicit)))))
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (364)) (Prims.of_int (15))
                                (Prims.of_int (364)) (Prims.of_int (61))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                  (Prims.of_int (365)) (Prims.of_int (2))
                                  (Prims.of_int (393)) (Prims.of_int (52)))))
                 with
                 | true ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                   (Prims.of_int (365))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (393))
                                                   (Prims.of_int (52))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (365))
                                             (Prims.of_int (11))
                                             (Prims.of_int (365))
                                             (Prims.of_int (23))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                       (Prims.of_int (366))
                                       (Prims.of_int (2))
                                       (Prims.of_int (393))
                                       (Prims.of_int (52)))))
                      with
                      | true ->
                          (match (reification eq m [] (const a) lhs)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                 (Prims.of_int (365))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (393))
                                                                 (Prims.of_int (52))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                           (Prims.of_int (365))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (365))
                                                           (Prims.of_int (23))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                     (Prims.of_int (366))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (393))
                                                     (Prims.of_int (52))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                               (Prims.of_int (366))
                                               (Prims.of_int (21))
                                               (Prims.of_int (366))
                                               (Prims.of_int (47))))))
                           with
                           | FStar_Tactics_Result.Success (a1, ps'1) ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                 (Prims.of_int (366))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (393))
                                                 (Prims.of_int (52)))))
                                with
                                | true ->
                                    ((match a1 with
                                      | (r1, ts, am) ->
                                          (fun ps1 ->
                                             match (reification eq m ts am
                                                      rhs)
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                 (Prims.of_int (367))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (367))
                                                                 (Prims.of_int (47))))))
                                             with
                                             | FStar_Tactics_Result.Success
                                                 (a2, ps'2) ->
                                                 (match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                   (Prims.of_int (367))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (393))
                                                                   (Prims.of_int (52)))))
                                                  with
                                                  | true ->
                                                      ((match a2 with
                                                        | (r2, uu___, am1) ->
                                                            (fun ps2 ->
                                                               match 
                                                                 FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                               with
                                                               | true ->
                                                                   (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__eq"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((convert_am
                                                                    am1),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((quote_exp
                                                                    r1),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((convert_am
                                                                    am1),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((quote_exp
                                                                    r2),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (51))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "monoid_reflect"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (25))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'4) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.iota;
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoidSimple.Equiv.canon";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.flatten";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.sort";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.select";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.primops])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (18))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__reflexivity"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    repeat_cong_right_identity
                                                                    eq m))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))))))
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (52)))))))
                                             | FStar_Tactics_Result.Failed
                                                 (e, ps'2) ->
                                                 FStar_Tactics_Result.Failed
                                                   (e, ps'2))))
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                  (Prims.of_int (366))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (393))
                                                  (Prims.of_int (52)))))))
                           | FStar_Tactics_Result.Failed (e, ps'1) ->
                               FStar_Tactics_Result.Failed (e, ps'1))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
let (canon_monoid :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun eq ->
    fun m ->
      fun ps ->
        match (FStar_Tactics_Builtins.norm
                 [FStar_Pervasives.iota; FStar_Pervasives.zeta])
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                            (Prims.of_int (397)) (Prims.of_int (2))
                            (Prims.of_int (397)) (Prims.of_int (19))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                              (Prims.of_int (398)) (Prims.of_int (2))
                              (Prims.of_int (415)) (Prims.of_int (68)))))
             with
             | true ->
                 (match (FStar_Tactics_Derived.cur_goal ())
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                            (Prims.of_int (398))
                                            (Prims.of_int (2))
                                            (Prims.of_int (415))
                                            (Prims.of_int (68))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (398))
                                      (Prims.of_int (10))
                                      (Prims.of_int (398))
                                      (Prims.of_int (21))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                        (Prims.of_int (400))
                                        (Prims.of_int (2))
                                        (Prims.of_int (415))
                                        (Prims.of_int (68)))))
                       with
                       | true ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                         (Prims.of_int (400))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (415))
                                                         (Prims.of_int (68))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                   (Prims.of_int (400))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (400))
                                                   (Prims.of_int (36))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (400))
                                             (Prims.of_int (2))
                                             (Prims.of_int (415))
                                             (Prims.of_int (68)))))
                            with
                            | true ->
                                ((match FStar_Reflection_Derived_Lemmas.collect_app_ref
                                          a1
                                  with
                                  | (sq, rel_xy) ->
                                      (match rel_xy with
                                       | (rel_xy1, uu___)::[] ->
                                           (fun ps1 ->
                                              match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (43))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                               (Prims.of_int (403))
                                                               (Prims.of_int (21))
                                                               (Prims.of_int (414))
                                                               (Prims.of_int (6)))))
                                              with
                                              | true ->
                                                  ((match FStar_Reflection_Derived_Lemmas.collect_app_ref
                                                            rel_xy1
                                                    with
                                                    | (rel, xy) ->
                                                        if
                                                          (FStar_List_Tot_Base.length
                                                             xy)
                                                            >=
                                                            (Prims.of_int (2))
                                                        then
                                                          (match ((FStar_List_Tot_Base.index
                                                                    xy
                                                                    ((FStar_List_Tot_Base.length
                                                                    xy) -
                                                                    (Prims.of_int (2)))),
                                                                   (FStar_List_Tot_Base.index
                                                                    xy
                                                                    ((FStar_List_Tot_Base.length
                                                                    xy) -
                                                                    Prims.int_one)))
                                                           with
                                                           | ((lhs,
                                                               FStar_Reflection_Data.Q_Explicit),
                                                              (rhs,
                                                               FStar_Reflection_Data.Q_Explicit))
                                                               ->
                                                               canon_lhs_rhs
                                                                 eq m lhs rhs
                                                           | uu___1 ->
                                                               FStar_Tactics_Derived.fail
                                                                 "Goal should have been an application of a binary relation to 2 explicit arguments")
                                                        else
                                                          FStar_Tactics_Derived.fail
                                                            "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"))
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps1
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (43))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                (Prims.of_int (403))
                                                                (Prims.of_int (21))
                                                                (Prims.of_int (414))
                                                                (Prims.of_int (6)))))))
                                       | uu___ ->
                                           FStar_Tactics_Derived.fail
                                             "Goal should be squash applied to a binary relation")))
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (400))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (415))
                                                          (Prims.of_int (68))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                    (Prims.of_int (400))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (400))
                                                    (Prims.of_int (36))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                              (Prims.of_int (400))
                                              (Prims.of_int (2))
                                              (Prims.of_int (415))
                                              (Prims.of_int (68))))))))
                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2 canon_monoid)
             FStar_Reflection_Embeddings.e_term
             FStar_Reflection_Embeddings.e_term
             FStar_Syntax_Embeddings.e_unit psc ncb args)