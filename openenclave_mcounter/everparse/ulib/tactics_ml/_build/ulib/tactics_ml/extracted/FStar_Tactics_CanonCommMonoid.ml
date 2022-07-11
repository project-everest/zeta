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
                       (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (32)) (Prims.of_int (24))
                          (Prims.of_int (32)) (Prims.of_int (36))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (32)) (Prims.of_int (21))
                            (Prims.of_int (32)) (Prims.of_int (48)))))
           with
           | true ->
               (if a
                then FStar_Tactics_Builtins.dump m
                else (fun s -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                             (Prims.of_int (32)) (Prims.of_int (21))
                             (Prims.of_int (32)) (Prims.of_int (48)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
type var = Prims.nat
type exp =
  | Unit 
  | Var of var 
  | Mult of exp * exp 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : exp -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let rec (exp_to_string : exp -> Prims.string) =
  fun e ->
    match e with
    | Unit -> "Unit"
    | Var x -> Prims.strcat "Var " (Prims.string_of_int x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type ('a, 'b) vmap = ((var * ('a * 'b)) Prims.list * ('a * 'b))
let const : 'a 'b . 'a -> 'b -> ('a, 'b) vmap =
  fun xa -> fun xb -> ([], (xa, xb))
let select : 'a 'b . var -> ('a, 'b) vmap -> 'a =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (a1, uu___) -> a1
      | uu___ -> FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd vm)
let select_extra : 'a 'b . var -> ('a, 'b) vmap -> 'b =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (uu___, b1) -> b1
      | uu___ -> FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd vm)
let update : 'a 'b . var -> 'a -> 'b -> ('a, 'b) vmap -> ('a, 'b) vmap =
  fun x ->
    fun xa ->
      fun xb ->
        fun vm ->
          (((x, (xa, xb)) :: (FStar_Pervasives_Native.fst vm)),
            (FStar_Pervasives_Native.snd vm))
let rec mdenote :
  'a 'b . 'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> exp -> 'a =
  fun m ->
    fun vm ->
      fun e ->
        match e with
        | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Var x -> select x vm
        | Mult (e1, e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m vm e1) (mdenote m vm e2)
let rec xsdenote :
  'a 'b .
    'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> var Prims.list -> 'a
  =
  fun m ->
    fun vm ->
      fun xs ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x vm
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x vm)
              (xsdenote m vm xs')
let rec (flatten : exp -> var Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Var x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)


type 'b permute =
  unit -> (Obj.t, 'b) vmap -> var Prims.list -> var Prims.list
type ('b, 'p) permute_correct = unit



type ('b, 'p) permute_via_swaps = unit


let (sort : unit permute) =
  fun a ->
    fun vm ->
      FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))
let sortWith : 'b . (Prims.nat -> Prims.nat -> Prims.int) -> 'b permute =
  fun f -> fun a -> fun vm -> FStar_List_Tot_Base.sortWith f






let canon : 'a 'b . ('a, 'b) vmap -> 'b permute -> exp -> var Prims.list =
  fun vm -> fun p -> fun e -> p () (Obj.magic vm) (flatten e)


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
  'a 'b .
    (FStar_Reflection_Types.term ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Reflection_Types.term Prims.list ->
        ('a, 'b) vmap ->
          (FStar_Reflection_Types.term ->
             FStar_Tactics_Types.proofstate ->
               'b FStar_Tactics_Result.__result)
            ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Tactics_Types.proofstate ->
                    (exp * FStar_Reflection_Types.term Prims.list * (
                      'a, 'b) vmap) FStar_Tactics_Result.__result
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun f ->
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
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (243))
                                         (Prims.of_int (15))
                                         (Prims.of_int (243))
                                         (Prims.of_int (32))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (243)) (Prims.of_int (2))
                                   (Prims.of_int (260)) (Prims.of_int (21)))))
                  with
                  | true ->
                      ((match FStar_Reflection_Derived_Lemmas.collect_app_ref
                                t
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
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (245))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (62))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                (Prims.of_int (250))
                                                (Prims.of_int (2))
                                                (Prims.of_int (260))
                                                (Prims.of_int (21)))))
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
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (21))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (33))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (18))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a1, ps') ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (250))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (250))
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
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (33))))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps') ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps')
                                    with
                                    | FStar_Tactics_Result.Success (a1, ps')
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (250))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (260))
                                                          (Prims.of_int (21)))))
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
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a2, ps'1) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))
                                                           with
                                                           | true ->
                                                               (if a2
                                                                then
                                                                  (fun ps3 ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm f
                                                                    mult unit
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (72))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | (e1,
                                                                    ts1, vm1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1 f
                                                                    mult unit
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (72))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
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
                                                                    vm2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (31)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                                else
                                                                  (match 
                                                                    where t
                                                                    ts
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    v ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Var v),
                                                                    ts, vm),
                                                                    s))
                                                                   | 
                                                                   FStar_Pervasives_Native.None
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (unquotea
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (58))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (f t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (58))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a3 a4
                                                                    vm),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Var
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    a4),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))))
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
                                                          ((Unit, ts, vm), s))
                                                   else
                                                     (match where t ts with
                                                      | FStar_Pervasives_Native.Some
                                                          v ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               (((Var v), ts,
                                                                  vm), s))
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          (fun ps2 ->
                                                             match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                             with
                                                             | true ->
                                                                 (match 
                                                                    (unquotea
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (58))))))
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (f t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (58))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a2 a3
                                                                    vm),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Var
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
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
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (250))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (260))
                                                           (Prims.of_int (21)))))))
                                    | FStar_Tactics_Result.Failed (e, ps') ->
                                        FStar_Tactics_Result.Failed (e, ps')))))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (243))
                                          (Prims.of_int (15))
                                          (Prims.of_int (243))
                                          (Prims.of_int (32))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (243)) (Prims.of_int (2))
                                    (Prims.of_int (260)) (Prims.of_int (21))))))
let reification :
  'b .
    (FStar_Reflection_Types.term ->
       FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'b ->
        unit ->
          (FStar_Reflection_Types.term ->
             FStar_Tactics_Types.proofstate ->
               Obj.t FStar_Tactics_Result.__result)
            ->
            (Obj.t ->
               FStar_Tactics_Types.proofstate ->
                 FStar_Reflection_Types.term FStar_Tactics_Result.__result)
              ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  Obj.t ->
                    FStar_Reflection_Types.term Prims.list ->
                      FStar_Tactics_Types.proofstate ->
                        (exp Prims.list * (Obj.t, 'b) vmap)
                          FStar_Tactics_Result.__result
  =
  fun f ->
    fun def ->
      fun a ->
        fun unquotea ->
          fun quotea ->
            fun tmult ->
              fun tunit ->
                fun munit ->
                  fun ts ->
                    fun ps ->
                      match (FStar_Tactics_Derived.norm_term
                               [FStar_Pervasives.delta;
                               FStar_Pervasives.zeta;
                               FStar_Pervasives.iota] tmult)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (267))
                                          (Prims.of_int (20))
                                          (Prims.of_int (267))
                                          (Prims.of_int (53))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoid.fst"
                                            (Prims.of_int (268))
                                            (Prims.of_int (2))
                                            (Prims.of_int (279))
                                            (Prims.of_int (30)))))
                           with
                           | true ->
                               (match (FStar_Tactics_Derived.norm_term
                                         [FStar_Pervasives.delta;
                                         FStar_Pervasives.zeta;
                                         FStar_Pervasives.iota] tunit)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (268))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (279))
                                                          (Prims.of_int (30))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (268))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (268))
                                                    (Prims.of_int (53))))))
                                with
                                | FStar_Tactics_Result.Success (a2, ps'1) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (269))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (279))
                                                      (Prims.of_int (30)))))
                                     with
                                     | true ->
                                         (match (FStar_Tactics_Util.map
                                                   (FStar_Tactics_Derived.norm_term
                                                      [FStar_Pervasives.delta;
                                                      FStar_Pervasives.zeta;
                                                      FStar_Pervasives.iota])
                                                   ts)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (269))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (269))
                                                              (Prims.of_int (62))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a3, ps'2) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (273))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (279))
                                                                (Prims.of_int (30)))))
                                               with
                                               | true ->
                                                   (match (FStar_Tactics_Util.fold_left
                                                             (fun uu___ ->
                                                                fun t ->
                                                                  match uu___
                                                                  with
                                                                  | (es, vs,
                                                                    vm) ->
                                                                    (fun ps1
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    vs vm f
                                                                    a1 a2 t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (70))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a4
                                                                    with
                                                                    | 
                                                                    (e, vs1,
                                                                    vm1) ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (20))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                             ([], [],
                                                               (const munit
                                                                  def)) a3)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (33))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a4, ps'3) ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30)))))
                                                         with
                                                         | true ->
                                                             FStar_Tactics_Result.Success
                                                               (((match a4
                                                                  with
                                                                  | (es,
                                                                    uu___,
                                                                    vm) ->
                                                                    ((FStar_List_Tot_Base.rev
                                                                    es), vm))),
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30))))))))
                                                    | FStar_Tactics_Result.Failed
                                                        (e, ps'3) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps'3)))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'2) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'2)))
                                | FStar_Tactics_Result.Failed (e, ps'1) ->
                                    FStar_Tactics_Result.Failed (e, ps'1)))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')
let rec (term_mem :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> Prims.bool)
  =
  fun x ->
    fun uu___ ->
      match uu___ with
      | [] -> false
      | hd::tl ->
          if FStar_Reflection_Builtins.term_eq hd x
          then true
          else term_mem x tl
let (unfold_topdown :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun ts ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                             (Prims.of_int (288)) (Prims.of_int (4))
                             (Prims.of_int (288)) (Prims.of_int (22))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                       (Prims.of_int (290)) (Prims.of_int (2))
                       (Prims.of_int (294)) (Prims.of_int (40)))))
      with
      | true ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (288))
                                              (Prims.of_int (4))
                                              (Prims.of_int (288))
                                              (Prims.of_int (22))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (290))
                                        (Prims.of_int (2))
                                        (Prims.of_int (294))
                                        (Prims.of_int (40))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommMonoid.fst"
                                  (Prims.of_int (291)) (Prims.of_int (4))
                                  (Prims.of_int (292)) (Prims.of_int (11))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (294)) (Prims.of_int (2))
                            (Prims.of_int (294)) (Prims.of_int (40)))))
           with
           | true ->
               (FStar_Tactics_Derived.topdown_rewrite
                  (fun s ->
                     fun s1 ->
                       FStar_Tactics_Result.Success
                         (((term_mem s ts), Prims.int_zero), s1))
                  (fun uu___ ->
                     fun ps1 ->
                       match (FStar_Tactics_Builtins.norm
                                [FStar_Pervasives.delta])
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (291))
                                           (Prims.of_int (4))
                                           (Prims.of_int (291))
                                           (Prims.of_int (16))))))
                       with
                       | FStar_Tactics_Result.Success (a, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (292))
                                             (Prims.of_int (4))
                                             (Prims.of_int (292))
                                             (Prims.of_int (11)))))
                            with
                            | true ->
                                (FStar_Tactics_Derived.trefl ())
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (292))
                                              (Prims.of_int (4))
                                              (Prims.of_int (292))
                                              (Prims.of_int (11)))))))
                       | FStar_Tactics_Result.Failed (e, ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (288))
                                               (Prims.of_int (4))
                                               (Prims.of_int (288))
                                               (Prims.of_int (22))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (290))
                                         (Prims.of_int (2))
                                         (Prims.of_int (294))
                                         (Prims.of_int (40))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (291)) (Prims.of_int (4))
                                   (Prims.of_int (292)) (Prims.of_int (11))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                             (Prims.of_int (294)) (Prims.of_int (2))
                             (Prims.of_int (294)) (Prims.of_int (40)))))))
let rec quote_list :
  'a .
    FStar_Reflection_Types.term ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           FStar_Reflection_Types.term FStar_Tactics_Result.__result)
        ->
        'a Prims.list ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.term FStar_Tactics_Result.__result
  =
  fun ta ->
    fun quotea ->
      fun xs ->
        match xs with
        | [] ->
            (fun s ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Derived.mk_app
                     (FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["Prims"; "Nil"])))
                     [(ta, FStar_Reflection_Data.Q_Implicit)]), s))
        | x::xs' ->
            (fun ps ->
               match match match match (quotea x)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (300))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (69))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (301))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (301))
                                                           (Prims.of_int (52))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (39))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (301))
                                                       (Prims.of_int (30))
                                                       (Prims.of_int (301))
                                                       (Prims.of_int (52)))))
                                      with
                                      | true ->
                                          FStar_Tactics_Result.Success
                                            ((a1,
                                               FStar_Reflection_Data.Q_Explicit),
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (301))
                                                          (Prims.of_int (30))
                                                          (Prims.of_int (301))
                                                          (Prims.of_int (52))))))))
                                 | FStar_Tactics_Result.Failed (e, ps') ->
                                     FStar_Tactics_Result.Failed (e, ps')
                           with
                           | FStar_Tactics_Result.Success (a1, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (300))
                                                 (Prims.of_int (29))
                                                 (Prims.of_int (302))
                                                 (Prims.of_int (69)))))
                                with
                                | true ->
                                    (match match match (quote_list ta quotea
                                                          xs')
                                                         (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (68))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (55))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a2, ps'1) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'1
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (68)))))
                                                      with
                                                      | true ->
                                                          FStar_Tactics_Result.Success
                                                            ((a2,
                                                               FStar_Reflection_Data.Q_Explicit),
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (68))))))))
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
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (300))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (69)))))
                                                with
                                                | true ->
                                                    FStar_Tactics_Result.Success
                                                      ([a2],
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))))
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
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (300))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (69)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((a1 :: a2),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (300))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (302))
                                                              (Prims.of_int (69))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps')
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (29))
                                           (Prims.of_int (302))
                                           (Prims.of_int (69)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (((ta, FStar_Reflection_Data.Q_Implicit) ::
                                  a1),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (300))
                                              (Prims.of_int (29))
                                              (Prims.of_int (302))
                                              (Prims.of_int (69))))))))
                     | FStar_Tactics_Result.Failed (e, ps') ->
                         FStar_Tactics_Result.Failed (e, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (300)) (Prims.of_int (14))
                                     (Prims.of_int (302)) (Prims.of_int (69)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["Prims"; "Cons"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (300))
                                        (Prims.of_int (14))
                                        (Prims.of_int (302))
                                        (Prims.of_int (69))))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let quote_vm :
  'a 'b .
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        ('a ->
           FStar_Tactics_Types.proofstate ->
             FStar_Reflection_Types.term FStar_Tactics_Result.__result)
          ->
          ('b ->
             FStar_Tactics_Types.proofstate ->
               FStar_Reflection_Types.term FStar_Tactics_Result.__result)
            ->
            ('a, 'b) vmap ->
              FStar_Tactics_Types.proofstate ->
                FStar_Reflection_Types.term FStar_Tactics_Result.__result
  =
  fun ta ->
    fun tb ->
      fun quotea ->
        fun quoteb ->
          fun vm ->
            fun ps ->
              match FStar_Tactics_Types.tracepoint
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (307)) (Prims.of_int (4))
                                     (Prims.of_int (308)) (Prims.of_int (70))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.CanonCommMonoid.fst"
                               (Prims.of_int (309)) (Prims.of_int (2))
                               (Prims.of_int (322)) (Prims.of_int (63)))))
              with
              | true ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (307))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (308))
                                                      (Prims.of_int (70))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                (Prims.of_int (309))
                                                (Prims.of_int (2))
                                                (Prims.of_int (322))
                                                (Prims.of_int (63))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (309))
                                          (Prims.of_int (19))
                                          (Prims.of_int (309))
                                          (Prims.of_int (45))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (310)) (Prims.of_int (2))
                                    (Prims.of_int (322)) (Prims.of_int (63)))))
                   with
                   | true ->
                       (match FStar_Tactics_Types.tracepoint
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
                                                                 ps
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (309))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (322))
                                                                 (Prims.of_int (63))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (309))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (309))
                                                           (Prims.of_int (45))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (310))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (322))
                                                     (Prims.of_int (63))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (311))
                                               (Prims.of_int (4))
                                               (Prims.of_int (313))
                                               (Prims.of_int (39))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (314))
                                         (Prims.of_int (2))
                                         (Prims.of_int (322))
                                         (Prims.of_int (63)))))
                        with
                        | true ->
                            (match FStar_Tactics_Types.tracepoint
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (45))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (311))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (313))
                                                                (Prims.of_int (39))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (314))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (322))
                                                          (Prims.of_int (63))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (314))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (314))
                                                    (Prims.of_int (55))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (315))
                                              (Prims.of_int (2))
                                              (Prims.of_int (322))
                                              (Prims.of_int (63)))))
                             with
                             | true ->
                                 (match (quote_list
                                           (FStar_Reflection_Derived.mk_e_app
                                              (FStar_Reflection_Builtins.pack_ln
                                                 (FStar_Reflection_Data.Tv_FVar
                                                    (FStar_Reflection_Builtins.pack_fv
                                                       ["FStar";
                                                       "Pervasives";
                                                       "Native";
                                                       "tuple2"])))
                                              [FStar_Reflection_Builtins.pack_ln
                                                 (FStar_Reflection_Data.Tv_FVar
                                                    (FStar_Reflection_Builtins.pack_fv
                                                       ["Prims"; "nat"]));
                                              FStar_Reflection_Derived.mk_e_app
                                                (FStar_Reflection_Builtins.pack_ln
                                                   (FStar_Reflection_Data.Tv_FVar
                                                      (FStar_Reflection_Builtins.pack_fv
                                                         ["FStar";
                                                         "Pervasives";
                                                         "Native";
                                                         "tuple2"])))
                                                [ta; tb]])
                                           (fun p ->
                                              fun ps1 ->
                                                match match match match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    (FStar_Reflection_Data.C_Int
                                                                    (FStar_Pervasives_Native.fst
                                                                    p))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (38))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1, ps')
                                                                    ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a1, ps')
                                                                    ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (26))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (quoteb
                                                                    (FStar_Pervasives_Native.snd
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (56))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a3,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a3],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2 ::
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((tb,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((ta,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1 ::
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a1, ps') ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                                 with
                                                                 | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((((FStar_Reflection_Derived.mk_e_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                    [ta; tb]),
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps') ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps')
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a1, ps') ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                           with
                                                           | true ->
                                                               FStar_Tactics_Result.Success
                                                                 ((((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "nat"]))),
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                   :: a1),
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps') ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps')
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a1, ps') ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))))
                                                     with
                                                     | true ->
                                                         FStar_Tactics_Result.Success
                                                           ((FStar_Reflection_Derived.mk_app
                                                               (FStar_Reflection_Builtins.pack_ln
                                                                  (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                               a1),
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e, ps') ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'))
                                           (FStar_Pervasives_Native.fst vm))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (45))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (314))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (314))
                                                                  (Prims.of_int (55))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoid.fst"
                                                            (Prims.of_int (315))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (322))
                                                            (Prims.of_int (63))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (57))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps') ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (317))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (322))
                                                        (Prims.of_int (63)))))
                                       with
                                       | true ->
                                           (match match match match match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (26))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (quoteb
                                                                    (FStar_Pervasives_Native.snd
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (56))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a3,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a3],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2 ::
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((tb,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                             with
                                                             | true ->
                                                                 FStar_Tactics_Result.Success
                                                                   (((ta,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70)))))
                                                       with
                                                       | true ->
                                                           FStar_Tactics_Result.Success
                                                             ((FStar_Reflection_Derived.mk_app
                                                                 (FStar_Reflection_Builtins.pack_ln
                                                                    (
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                 a2),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
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
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (321))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (322))
                                                                  (Prims.of_int (63)))))
                                                 with
                                                 | true ->
                                                     FStar_Tactics_Result.Success
                                                       ((FStar_Reflection_Derived.mk_app
                                                           (FStar_Reflection_Builtins.pack_ln
                                                              (FStar_Reflection_Data.Tv_FVar
                                                                 (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                           [((FStar_Reflection_Derived.mk_e_app
                                                                (FStar_Reflection_Builtins.pack_ln
                                                                   (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"])))
                                                                [FStar_Reflection_Derived.mk_e_app
                                                                   (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                   [FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "nat"]));
                                                                   FStar_Reflection_Derived.mk_e_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                    [ta; tb]]]),
                                                              FStar_Reflection_Data.Q_Implicit);
                                                           ((FStar_Reflection_Derived.mk_e_app
                                                               (FStar_Reflection_Builtins.pack_ln
                                                                  (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                               [ta; tb]),
                                                             FStar_Reflection_Data.Q_Implicit);
                                                           (a1,
                                                             FStar_Reflection_Data.Q_Explicit);
                                                           (a2,
                                                             FStar_Reflection_Data.Q_Explicit)]),
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'1) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'1)))
                                  | FStar_Tactics_Result.Failed (e, ps') ->
                                      FStar_Tactics_Result.Failed (e, ps')))))
let rec (quote_exp :
  exp ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun e ->
    match e with
    | Unit ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"]))), s))
    | Var x ->
        (fun ps ->
           match match (FStar_Tactics_Builtins.pack
                          (FStar_Reflection_Data.Tv_Const
                             (FStar_Reflection_Data.C_Int x)))
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (327))
                                           (Prims.of_int (29))
                                           (Prims.of_int (327))
                                           (Prims.of_int (56))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (327)) (Prims.of_int (30))
                                     (Prims.of_int (327)) (Prims.of_int (55))))))
                 with
                 | FStar_Tactics_Result.Success (a, ps') ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (327))
                                       (Prims.of_int (29))
                                       (Prims.of_int (327))
                                       (Prims.of_int (56)))))
                      with
                      | true ->
                          FStar_Tactics_Result.Success
                            ([a],
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (327))
                                          (Prims.of_int (29))
                                          (Prims.of_int (327))
                                          (Prims.of_int (56))))))))
                 | FStar_Tactics_Result.Failed (e1, ps') ->
                     FStar_Tactics_Result.Failed (e1, ps')
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (327)) (Prims.of_int (13))
                                 (Prims.of_int (327)) (Prims.of_int (56)))))
                with
                | true ->
                    FStar_Tactics_Result.Success
                      ((FStar_Reflection_Derived.mk_e_app
                          (FStar_Reflection_Builtins.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "CanonCommMonoid";
                                   "Var"]))) a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (327)) (Prims.of_int (13))
                                    (Prims.of_int (327)) (Prims.of_int (56))))))))
           | FStar_Tactics_Result.Failed (e1, ps') ->
               FStar_Tactics_Result.Failed (e1, ps'))
    | Mult (e1, e2) ->
        (fun ps ->
           match match (quote_exp e1)
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (328))
                                           (Prims.of_int (35))
                                           (Prims.of_int (328))
                                           (Prims.of_int (63))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (328)) (Prims.of_int (36))
                                     (Prims.of_int (328)) (Prims.of_int (48))))))
                 with
                 | FStar_Tactics_Result.Success (a, ps') ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (328))
                                       (Prims.of_int (35))
                                       (Prims.of_int (328))
                                       (Prims.of_int (63)))))
                      with
                      | true ->
                          (match match (quote_exp e2)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (328))
                                                                 (Prims.of_int (35))
                                                                 (Prims.of_int (328))
                                                                 (Prims.of_int (63))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (328))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (328))
                                                           (Prims.of_int (63))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (328))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (328))
                                                     (Prims.of_int (62))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (328))
                                                       (Prims.of_int (35))
                                                       (Prims.of_int (328))
                                                       (Prims.of_int (63)))))
                                      with
                                      | true ->
                                          FStar_Tactics_Result.Success
                                            ([a1],
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (328))
                                                          (Prims.of_int (35))
                                                          (Prims.of_int (328))
                                                          (Prims.of_int (63))))))))
                                 | FStar_Tactics_Result.Failed (e3, ps'1) ->
                                     FStar_Tactics_Result.Failed (e3, ps'1)
                           with
                           | FStar_Tactics_Result.Success (a1, ps'1) ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (328))
                                                 (Prims.of_int (35))
                                                 (Prims.of_int (328))
                                                 (Prims.of_int (63)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ((a :: a1),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (328))
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (328))
                                                    (Prims.of_int (63))))))))
                           | FStar_Tactics_Result.Failed (e3, ps'1) ->
                               FStar_Tactics_Result.Failed (e3, ps'1)))
                 | FStar_Tactics_Result.Failed (e3, ps') ->
                     FStar_Tactics_Result.Failed (e3, ps')
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (328)) (Prims.of_int (18))
                                 (Prims.of_int (328)) (Prims.of_int (63)))))
                with
                | true ->
                    FStar_Tactics_Result.Success
                      ((FStar_Reflection_Derived.mk_e_app
                          (FStar_Reflection_Builtins.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "CanonCommMonoid";
                                   "Mult"]))) a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (328)) (Prims.of_int (18))
                                    (Prims.of_int (328)) (Prims.of_int (63))))))))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
let canon_monoid_aux :
  'a 'b .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        ('a ->
           FStar_Tactics_Types.proofstate ->
             FStar_Reflection_Types.term FStar_Tactics_Result.__result)
          ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                'a ->
                  FStar_Reflection_Types.term ->
                    ('b ->
                       FStar_Tactics_Types.proofstate ->
                         FStar_Reflection_Types.term
                           FStar_Tactics_Result.__result)
                      ->
                      (FStar_Reflection_Types.term ->
                         FStar_Tactics_Types.proofstate ->
                           'b FStar_Tactics_Result.__result)
                        ->
                        'b ->
                          FStar_Reflection_Types.term ->
                            FStar_Reflection_Types.term ->
                              FStar_Tactics_Types.proofstate ->
                                unit FStar_Tactics_Result.__result
  =
  fun ta ->
    fun unquotea ->
      fun quotea ->
        fun tm ->
          fun tmult ->
            fun tunit ->
              fun munit ->
                fun tb ->
                  fun quoteb ->
                    fun f ->
                      fun def ->
                        fun tp ->
                          fun tpc ->
                            fun ps ->
                              match (FStar_Tactics_Builtins.norm [])
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (335))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (335))
                                                  (Prims.of_int (9))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps') ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (42)))))
                                   with
                                   | true ->
                                       (match match (FStar_Tactics_Derived.cur_goal
                                                       ())
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (42))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (37))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (24))
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (37))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'1) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (37)))))
                                                   with
                                                   | true ->
                                                       (FStar_Reflection_Formula.term_as_formula
                                                          a2)
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (37)))))))
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
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (336))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (407))
                                                              (Prims.of_int (42)))))
                                             with
                                             | true ->
                                                 ((match a2 with
                                                   | FStar_Reflection_Formula.Comp
                                                       (FStar_Reflection_Formula.Eq
                                                        (FStar_Pervasives_Native.Some
                                                        t), t1, t2)
                                                       ->
                                                       if
                                                         FStar_Reflection_Builtins.term_eq
                                                           t ta
                                                       then
                                                         (fun ps1 ->
                                                            match Obj.magic
                                                                    (
                                                                    (reification
                                                                    f def ()
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun uu___
                                                                    ->
                                                                    (Obj.magic
                                                                    unquotea)
                                                                    uu___1
                                                                    uu___)
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun uu___
                                                                    ->
                                                                    (Obj.magic
                                                                    quotea)
                                                                    uu___1
                                                                    uu___)
                                                                    tmult
                                                                    tunit
                                                                    (Obj.magic
                                                                    munit)
                                                                    [t1; t2])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (75)))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a3, ps'2) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (32)))))
                                                                 with
                                                                 | true ->
                                                                    ((match a3
                                                                    with
                                                                    | (r1::r2::[],
                                                                    vm) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (quote_vm
                                                                    ta tb
                                                                    quotea
                                                                    quoteb vm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (51))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (quote_exp
                                                                    r1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (32))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (quote_exp
                                                                    r2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (32))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
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
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (83))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a4,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a5,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a4,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a6,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (83))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (23))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.mapply
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "monoid_reflect"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tp,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tpc,
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (63))))))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (unfold_topdown
                                                                    [
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "canon"]));
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "xsdenote"]));
                                                                    tp])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (52))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a9,
                                                                    ps'8) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoid.canon";
                                                                    "FStar.Tactics.CanonCommMonoid.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoid.flatten";
                                                                    "FStar.Tactics.CanonCommMonoid.select";
                                                                    "FStar.Tactics.CanonCommMonoid.select_extra";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_list";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_vm";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_exp";
                                                                    "FStar.Tactics.CanonCommMonoid.const_compare";
                                                                    "FStar.Tactics.CanonCommMonoid.special_compare";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.snd";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "SL.AutoTactic.compare_b";
                                                                    "SL.AutoTactic.compare_v";
                                                                    "FStar.Order.int_of_order";
                                                                    "FStar.Reflection.Derived.compare_term";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota;
                                                                    FStar_Pervasives.primops])
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)))
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
                                                                    (e, ps'6))))
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
                                                                    (e, ps'3))
                                                                    | uu___
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (32)))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps'2) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'2))
                                                       else
                                                         FStar_Tactics_Derived.fail
                                                           "Goal should be an equality at the right monoid type"
                                                   | uu___ ->
                                                       FStar_Tactics_Derived.fail
                                                         "Goal should be an equality"))
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoid.fst"
                                                               (Prims.of_int (336))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (407))
                                                               (Prims.of_int (42)))))))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps'1) ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps'1)))
                              | FStar_Tactics_Result.Failed (e, ps') ->
                                  FStar_Tactics_Result.Failed (e, ps')
let canon_monoid_with :
  'b .
    (FStar_Reflection_Types.term ->
       FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'b ->
        'b permute ->
          unit ->
            unit ->
              Obj.t FStar_Algebra_CommMonoid.cm ->
                FStar_Tactics_Types.proofstate ->
                  unit FStar_Tactics_Result.__result
  =
  fun f ->
    fun def ->
      fun p ->
        fun pc ->
          fun a ->
            fun m ->
              fun ps ->
                match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (413))
                                       (Prims.of_int (4))
                                       (Prims.of_int (413))
                                       (Prims.of_int (13))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (412)) (Prims.of_int (2))
                                 (Prims.of_int (415)) (Prims.of_int (63)))))
                with
                | true ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (413))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (413))
                                                        (Prims.of_int (13))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (412))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (415))
                                                  (Prims.of_int (63))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommMonoid.fst"
                                            (Prims.of_int (414))
                                            (Prims.of_int (4))
                                            (Prims.of_int (414))
                                            (Prims.of_int (13))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoid.fst"
                                      (Prims.of_int (412)) (Prims.of_int (2))
                                      (Prims.of_int (415))
                                      (Prims.of_int (63)))))
                     with
                     | true ->
                         (match FStar_Tactics_Types.tracepoint
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
                                                                   ps
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (412))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (415))
                                                                   (Prims.of_int (63))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommMonoid.fst"
                                                             (Prims.of_int (414))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (414))
                                                             (Prims.of_int (13))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (412))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (415))
                                                       (Prims.of_int (63))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (414))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (414))
                                                 (Prims.of_int (34))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (412))
                                           (Prims.of_int (2))
                                           (Prims.of_int (415))
                                           (Prims.of_int (63)))))
                          with
                          | true ->
                              (match FStar_Tactics_Types.tracepoint
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (414))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (414))
                                                                  (Prims.of_int (34))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoid.fst"
                                                            (Prims.of_int (412))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (415))
                                                            (Prims.of_int (63))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (414))
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (414))
                                                      (Prims.of_int (55))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                (Prims.of_int (412))
                                                (Prims.of_int (2))
                                                (Prims.of_int (415))
                                                (Prims.of_int (63)))))
                               with
                               | true ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
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
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (55))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (412))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (415))
                                                                 (Prims.of_int (63))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (415))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (415))
                                                           (Prims.of_int (13))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (412))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (415))
                                                     (Prims.of_int (63)))))
                                    with
                                    | true ->
                                        (match FStar_Tactics_Types.tracepoint
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
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (55))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (13))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (415))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (415))
                                                                (Prims.of_int (52))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (412))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (415))
                                                          (Prims.of_int (63)))))
                                         with
                                         | true ->
                                             (match FStar_Tactics_Types.tracepoint
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (55))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoid.fst"
                                                               (Prims.of_int (412))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (415))
                                                               (Prims.of_int (63)))))
                                              with
                                              | true ->
                                                  (canon_monoid_aux
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     FStar_Tactics_Builtins.unquote
                                                     (fun x ->
                                                        fun s ->
                                                          FStar_Tactics_Result.Success
                                                            ((Obj.magic
                                                                (failwith
                                                                   "Cannot evaluate open quotation at runtime")),
                                                              s))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                        m)
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (fun x ->
                                                        fun s ->
                                                          FStar_Tactics_Result.Success
                                                            ((Obj.magic
                                                                (failwith
                                                                   "Cannot evaluate open quotation at runtime")),
                                                              s)) f def
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime")))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (55))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (412))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (415))
                                                                (Prims.of_int (63))))))))))))
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun cm ->
    canon_monoid_with
      (fun uu___ -> fun s -> FStar_Tactics_Result.Success ((), s)) ()
      (fun a1 -> sort ()) () () (Obj.magic cm)

let (is_const :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (433)) (Prims.of_int (45))
                          (Prims.of_int (433)) (Prims.of_int (56))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (433)) (Prims.of_int (35))
                            (Prims.of_int (433)) (Prims.of_int (56)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Data.uu___is_Tv_Const a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.CanonCommMonoid.fst"
                               (Prims.of_int (433)) (Prims.of_int (35))
                               (Prims.of_int (433)) (Prims.of_int (56))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let const_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> Prims.int_one
        | (true, false) -> (Prims.of_int (-1))
let const_last :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (const_compare vm) xs
let canon_monoid_const :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun cm ->
    canon_monoid_with is_const false (fun a1 -> const_last) () ()
      (Obj.magic cm)

let (is_special :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun ts ->
    fun t -> fun s -> FStar_Tactics_Result.Success ((term_mem t ts), s)
let special_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> Prims.int_zero
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> (Prims.of_int (-1))
        | (true, false) -> Prims.int_one
let special_first :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (special_compare vm) xs

let canon_monoid_special :
  'uuuuu .
    FStar_Reflection_Types.term Prims.list ->
      'uuuuu FStar_Algebra_CommMonoid.cm ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ts ->
           Obj.magic
             (canon_monoid_with (is_special ts) false
                (fun a -> special_first) () ())) uu___2 uu___1 uu___
