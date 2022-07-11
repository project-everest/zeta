open Prims
let (dump :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun m ->
    fun ps ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (34)) (Prims.of_int (16))
                          (Prims.of_int (34)) (Prims.of_int (28))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                            (Prims.of_int (34)) (Prims.of_int (13))
                            (Prims.of_int (34)) (Prims.of_int (40)))))
           with
           | true ->
               (if a
                then FStar_Tactics_Builtins.dump m
                else (fun s -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "FStar.Tactics.CanonCommMonoidSimple.fst"
                             (Prims.of_int (34)) (Prims.of_int (13))
                             (Prims.of_int (34)) (Prims.of_int (40)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
type atom = Prims.nat
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
let rec mdenote : 'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> exp -> 'a
  =
  fun m ->
    fun am ->
      fun e ->
        match e with
        | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Atom x -> select x am
        | Mult (e1, e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m am e1) (mdenote m am e2)
let rec xsdenote :
  'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> atom Prims.list -> 'a =
  fun m ->
    fun am ->
      fun xs ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x am
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x am)
              (xsdenote m am xs')
let rec (flatten : exp -> atom Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Atom x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)


type permute = atom Prims.list -> atom Prims.list
type 'p permute_correct = unit



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
let rec reification_aux :
  'a .
    FStar_Reflection_Types.term Prims.list ->
      'a amap ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Tactics_Types.proofstate ->
                (exp * FStar_Reflection_Types.term Prims.list * 'a amap)
                  FStar_Tactics_Result.__result
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
                                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                                     (Prims.of_int (221)) (Prims.of_int (15))
                                     (Prims.of_int (221)) (Prims.of_int (32))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                               (Prims.of_int (221)) (Prims.of_int (2))
                               (Prims.of_int (238)) (Prims.of_int (22)))))
              with
              | true ->
                  ((match FStar_Reflection_Derived_Lemmas.collect_app_ref t
                    with
                    | (hd, tl) ->
                        (fun ps1 ->
                           match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                  (Prims.of_int (223))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (226))
                                                  (Prims.of_int (57))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (228))
                                            (Prims.of_int (2))
                                            (Prims.of_int (238))
                                            (Prims.of_int (22)))))
                           with
                           | true ->
                               (match match (FStar_Tactics_Builtins.inspect
                                               hd)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (22))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (228))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (228))
                                                                (Prims.of_int (33))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (228))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (228))
                                                          (Prims.of_int (18))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps') ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                            (Prims.of_int (228))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (228))
                                                            (Prims.of_int (33)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((a1,
                                                    (FStar_List_Tot_Base.list_unref
                                                       tl)),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                               (Prims.of_int (228))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (228))
                                                               (Prims.of_int (33))))))))
                                      | FStar_Tactics_Result.Failed (e, ps')
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps')
                                with
                                | FStar_Tactics_Result.Success (a1, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (228))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (238))
                                                      (Prims.of_int (22)))))
                                     with
                                     | true ->
                                         ((match a1 with
                                           | (FStar_Reflection_Data.Tv_FVar
                                              fv,
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
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (34))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a2, ps'1) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (39)))))
                                                             with
                                                             | true ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((FStar_Reflection_Builtins.term_eq
                                                                    a2 mult),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (39))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a2, ps'1) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (22)))))
                                                       with
                                                       | true ->
                                                           (if a2
                                                            then
                                                              (fun ps3 ->
                                                                 match 
                                                                   (reification_aux
                                                                    ts am
                                                                    mult unit
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (61))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
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
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (61))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a4
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
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (233))
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
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (31)))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                            else
                                                              (match 
                                                                 where t ts
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   v ->
                                                                   (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom v),
                                                                    ts, am),
                                                                    s))
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   (fun ps3
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.unquote
                                                                    t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (57))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    (update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a3 am)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))))
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (234))
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
                                               else
                                                 (match where t ts with
                                                  | FStar_Pervasives_Native.Some
                                                      v ->
                                                      (fun s ->
                                                         FStar_Tactics_Result.Success
                                                           (((Atom v), ts,
                                                              am), s))
                                                  | FStar_Pervasives_Native.None
                                                      ->
                                                      (fun ps2 ->
                                                         match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (36))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57)))))
                                                         with
                                                         | true ->
                                                             (match (FStar_Tactics_Builtins.unquote
                                                                    t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (57))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a2, ps'1)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    (update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a2 am)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (57))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1))))))
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                       (Prims.of_int (228))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (238))
                                                       (Prims.of_int (22)))))))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')))))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (221))
                                      (Prims.of_int (15))
                                      (Prims.of_int (221))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (221)) (Prims.of_int (2))
                                (Prims.of_int (238)) (Prims.of_int (22))))))
let reification :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Reflection_Types.term Prims.list ->
        'a amap ->
          FStar_Reflection_Types.term ->
            FStar_Tactics_Types.proofstate ->
              (exp * FStar_Reflection_Types.term Prims.list * 'a amap)
                FStar_Tactics_Result.__result
  =
  fun m ->
    fun ts ->
      fun am ->
        fun t ->
          fun ps ->
            match match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                                               (Prims.of_int (242))
                                               (Prims.of_int (13))
                                               (Prims.of_int (242))
                                               (Prims.of_int (61))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                                         (Prims.of_int (242))
                                         (Prims.of_int (41))
                                         (Prims.of_int (242))
                                         (Prims.of_int (61))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommMonoidSimple.fst"
                                   (Prims.of_int (242)) (Prims.of_int (13))
                                   (Prims.of_int (242)) (Prims.of_int (61)))))
                  with
                  | true ->
                      (FStar_Tactics_Derived.norm_term
                         [FStar_Pervasives.delta;
                         FStar_Pervasives.zeta;
                         FStar_Pervasives.iota]
                         (Obj.magic
                            (failwith
                               "Cannot evaluate open quotation at runtime")))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (242))
                                                (Prims.of_int (13))
                                                (Prims.of_int (242))
                                                (Prims.of_int (61))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                          (Prims.of_int (242))
                                          (Prims.of_int (41))
                                          (Prims.of_int (242))
                                          (Prims.of_int (61))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                    (Prims.of_int (242)) (Prims.of_int (13))
                                    (Prims.of_int (242)) (Prims.of_int (61))))))
            with
            | FStar_Tactics_Result.Success (a1, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommMonoidSimple.fst"
                                  (Prims.of_int (243)) (Prims.of_int (2))
                                  (Prims.of_int (245)) (Prims.of_int (35)))))
                 with
                 | true ->
                     (match match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                               (Prims.of_int (243))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (245))
                                                               (Prims.of_int (35))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                         (Prims.of_int (243))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (243))
                                                         (Prims.of_int (61))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                   (Prims.of_int (243))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (243))
                                                   (Prims.of_int (61))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.fst"
                                             (Prims.of_int (243))
                                             (Prims.of_int (13))
                                             (Prims.of_int (243))
                                             (Prims.of_int (61)))))
                            with
                            | true ->
                                (FStar_Tactics_Derived.norm_term
                                   [FStar_Pervasives.delta;
                                   FStar_Pervasives.zeta;
                                   FStar_Pervasives.iota]
                                   (Obj.magic
                                      (failwith
                                         "Cannot evaluate open quotation at runtime")))
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (245))
                                                                (Prims.of_int (35))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (61))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                    (Prims.of_int (243))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (243))
                                                    (Prims.of_int (61))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (243))
                                              (Prims.of_int (13))
                                              (Prims.of_int (243))
                                              (Prims.of_int (61))))))
                      with
                      | FStar_Tactics_Result.Success (a2, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (244))
                                            (Prims.of_int (2))
                                            (Prims.of_int (245))
                                            (Prims.of_int (35)))))
                           with
                           | true ->
                               (match (FStar_Tactics_Derived.norm_term
                                         [FStar_Pervasives.delta;
                                         FStar_Pervasives.zeta;
                                         FStar_Pervasives.iota] t)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (244))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (245))
                                                          (Prims.of_int (35))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                    (Prims.of_int (244))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (244))
                                                    (Prims.of_int (42))))))
                                with
                                | FStar_Tactics_Result.Success (a3, ps'2) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (245))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (245))
                                                      (Prims.of_int (35)))))
                                     with
                                     | true ->
                                         (reification_aux ts am a1 a2 a3)
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'2
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                       (Prims.of_int (245))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (245))
                                                       (Prims.of_int (35)))))))
                                | FStar_Tactics_Result.Failed (e, ps'2) ->
                                    FStar_Tactics_Result.Failed (e, ps'2)))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun m ->
    fun ps ->
      match (FStar_Tactics_Builtins.norm [])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (248)) (Prims.of_int (2))
                          (Prims.of_int (248)) (Prims.of_int (9))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                            (Prims.of_int (249)) (Prims.of_int (2))
                            (Prims.of_int (272)) (Prims.of_int (42)))))
           with
           | true ->
               (match match (FStar_Tactics_Derived.cur_goal ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (249))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (272))
                                                      (Prims.of_int (42))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (249))
                                                (Prims.of_int (8))
                                                (Prims.of_int (249))
                                                (Prims.of_int (37))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                          (Prims.of_int (249))
                                          (Prims.of_int (24))
                                          (Prims.of_int (249))
                                          (Prims.of_int (37))))))
                      with
                      | FStar_Tactics_Result.Success (a2, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (249))
                                            (Prims.of_int (8))
                                            (Prims.of_int (249))
                                            (Prims.of_int (37)))))
                           with
                           | true ->
                               (FStar_Reflection_Formula.term_as_formula a2)
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.fst"
                                             (Prims.of_int (249))
                                             (Prims.of_int (8))
                                             (Prims.of_int (249))
                                             (Prims.of_int (37)))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)
                with
                | FStar_Tactics_Result.Success (a2, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (249)) (Prims.of_int (2))
                                      (Prims.of_int (272))
                                      (Prims.of_int (42)))))
                     with
                     | true ->
                         ((match a2 with
                           | FStar_Reflection_Formula.Comp
                               (FStar_Reflection_Formula.Eq
                                (FStar_Pervasives_Native.Some t), t1, t2)
                               ->
                               (fun ps1 ->
                                  match match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (28))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                               (Prims.of_int (253))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (253))
                                                               (Prims.of_int (28))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                         (Prims.of_int (253))
                                                         (Prims.of_int (9))
                                                         (Prims.of_int (253))
                                                         (Prims.of_int (28)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((FStar_Reflection_Builtins.term_eq
                                                  t
                                                  (Obj.magic
                                                     (failwith
                                                        "Cannot evaluate open quotation at runtime"))),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (28))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                  (Prims.of_int (253))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (253))
                                                                  (Prims.of_int (28))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                            (Prims.of_int (253))
                                                            (Prims.of_int (9))
                                                            (Prims.of_int (253))
                                                            (Prims.of_int (28)))))))
                                  with
                                  | FStar_Tactics_Result.Success (a3, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                        (Prims.of_int (253))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (271))
                                                        (Prims.of_int (69)))))
                                       with
                                       | true ->
                                           (if a3
                                            then
                                              (fun ps2 ->
                                                 match (reification m []
                                                          (const
                                                             (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                                m)) t1)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (67))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))
                                                      with
                                                      | true ->
                                                          ((match a4 with
                                                            | (r1, ts, am) ->
                                                                (fun ps3 ->
                                                                   match 
                                                                    (reification
                                                                    m ts am
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (48))))))
                                                                   with
                                                                   | 
                                                                   FStar_Tactics_Result.Success
                                                                    (a5,
                                                                    ps'4) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | (r2,
                                                                    uu___,
                                                                    am1) ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_to_string
                                                                    (Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49)))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((Prims.strcat
                                                                    "am =" a6),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (dump a6)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (50)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime")))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (62))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'6) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))
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
                                                                    "monoid_reflect"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (31))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoidSimple.canon";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.flatten";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.sort";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.select";
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (22)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3))
                                            else
                                              FStar_Tactics_Derived.fail
                                                "Goal should be an equality at the right monoid type")
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                         (Prims.of_int (253))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (271))
                                                         (Prims.of_int (69)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))
                           | uu___ ->
                               FStar_Tactics_Derived.fail
                                 "Goal should be an equality"))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                       (Prims.of_int (249))
                                       (Prims.of_int (2))
                                       (Prims.of_int (272))
                                       (Prims.of_int (42)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

