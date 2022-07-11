open Prims
let (fresh_bv :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.bv FStar_Tactics_Result.__result)
  = FStar_Tactics_Builtins.fresh_bv_named "x"
type comparison =
  | Eq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let (uu___is_Eq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Eq _0 -> true | uu___ -> false
let (__proj__Eq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Eq _0 -> _0
let (uu___is_BoolEq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | BoolEq _0 -> true | uu___ -> false
let (__proj__BoolEq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | BoolEq _0 -> _0
let (uu___is_Lt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Le : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Le -> true | uu___ -> false
let (uu___is_Gt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (uu___is_Ge : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Ge -> true | uu___ -> false
type formula =
  | True_ 
  | False_ 
  | Comp of comparison * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term 
  | And of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Or of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Not of FStar_Reflection_Types.term 
  | Implies of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Iff of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Forall of FStar_Reflection_Types.bv * FStar_Reflection_Types.term 
  | Exists of FStar_Reflection_Types.bv * FStar_Reflection_Types.term 
  | App of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Name of FStar_Reflection_Types.bv 
  | FV of FStar_Reflection_Types.fv 
  | IntLit of Prims.int 
  | F_Unknown 
let (uu___is_True_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | True_ -> true | uu___ -> false
let (uu___is_False_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | False_ -> true | uu___ -> false
let (uu___is_Comp : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp (_0, _1, _2) -> true | uu___ -> false
let (__proj__Comp__item___0 : formula -> comparison) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _0
let (__proj__Comp__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _1
let (__proj__Comp__item___2 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _2
let (uu___is_And : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | And (_0, _1) -> true | uu___ -> false
let (__proj__And__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _0
let (__proj__And__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _1
let (uu___is_Or : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Or (_0, _1) -> true | uu___ -> false
let (__proj__Or__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _0
let (__proj__Or__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _1
let (uu___is_Not : formula -> Prims.bool) =
  fun projectee -> match projectee with | Not _0 -> true | uu___ -> false
let (__proj__Not__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Not _0 -> _0
let (uu___is_Implies : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Implies (_0, _1) -> true | uu___ -> false
let (__proj__Implies__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _0
let (__proj__Implies__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _1
let (uu___is_Iff : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Iff (_0, _1) -> true | uu___ -> false
let (__proj__Iff__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _0
let (__proj__Iff__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _1
let (uu___is_Forall : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Forall (_0, _1) -> true | uu___ -> false
let (__proj__Forall__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Forall (_0, _1) -> _0
let (__proj__Forall__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Forall (_0, _1) -> _1
let (uu___is_Exists : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Exists (_0, _1) -> true | uu___ -> false
let (__proj__Exists__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Exists (_0, _1) -> _0
let (__proj__Exists__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Exists (_0, _1) -> _1
let (uu___is_App : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | App (_0, _1) -> true | uu___ -> false
let (__proj__App__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _0
let (__proj__App__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _1
let (uu___is_Name : formula -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_FV : formula -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu___ -> false
let (__proj__FV__item___0 : formula -> FStar_Reflection_Types.fv) =
  fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_IntLit : formula -> Prims.bool) =
  fun projectee -> match projectee with | IntLit _0 -> true | uu___ -> false
let (__proj__IntLit__item___0 : formula -> Prims.int) =
  fun projectee -> match projectee with | IntLit _0 -> _0
let (uu___is_F_Unknown : formula -> Prims.bool) =
  fun projectee -> match projectee with | F_Unknown -> true | uu___ -> false
let (mk_Forall :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> formula FStar_Tactics_Result.__result)
  =
  fun typ ->
    fun pred ->
      fun s ->
        FStar_Tactics_Result.Success
          ((Forall
              ((FStar_Reflection_Builtins.pack_bv
                  {
                    FStar_Reflection_Data.bv_ppname = "x";
                    FStar_Reflection_Data.bv_index = Prims.int_zero;
                    FStar_Reflection_Data.bv_sort = typ
                  }),
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_App
                      (pred,
                        ((FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_BVar
                               (FStar_Reflection_Builtins.pack_bv
                                  {
                                    FStar_Reflection_Data.bv_ppname = "x";
                                    FStar_Reflection_Data.bv_index =
                                      Prims.int_zero;
                                    FStar_Reflection_Data.bv_sort = typ
                                  }))), FStar_Reflection_Data.Q_Explicit)))))),
            s)
let (mk_Exists :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> formula FStar_Tactics_Result.__result)
  =
  fun typ ->
    fun pred ->
      fun s ->
        FStar_Tactics_Result.Success
          ((Exists
              ((FStar_Reflection_Builtins.pack_bv
                  {
                    FStar_Reflection_Data.bv_ppname = "x";
                    FStar_Reflection_Data.bv_index = Prims.int_zero;
                    FStar_Reflection_Data.bv_sort = typ
                  }),
                (FStar_Reflection_Builtins.pack_ln
                   (FStar_Reflection_Data.Tv_App
                      (pred,
                        ((FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_BVar
                               (FStar_Reflection_Builtins.pack_bv
                                  {
                                    FStar_Reflection_Data.bv_ppname = "x";
                                    FStar_Reflection_Data.bv_index =
                                      Prims.int_zero;
                                    FStar_Reflection_Data.bv_sort = typ
                                  }))), FStar_Reflection_Data.Q_Explicit)))))),
            s)
let (term_as_formula' :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> formula FStar_Tactics_Result.__result)
  =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_Var n ->
        (fun s -> FStar_Tactics_Result.Success ((Name n), s))
    | FStar_Reflection_Data.Tv_FVar fv ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((if
                 (FStar_Reflection_Builtins.inspect_fv fv) =
                   FStar_Reflection_Const.true_qn
               then True_
               else
                 if
                   (FStar_Reflection_Builtins.inspect_fv fv) =
                     FStar_Reflection_Const.false_qn
                 then False_
                 else FV fv), s))
    | FStar_Reflection_Data.Tv_App (h0, t1) ->
        (fun ps ->
           match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Reflection.Formula.fst"
                                  (Prims.of_int (79)) (Prims.of_int (22))
                                  (Prims.of_int (79)) (Prims.of_int (36))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (79)) (Prims.of_int (8))
                            (Prims.of_int (111)) (Prims.of_int (26)))))
           with
           | true ->
               ((match FStar_Reflection_Derived.collect_app h0 with
                 | (h, ts) ->
                     (match ((FStar_Reflection_Builtins.inspect_ln h),
                              (FStar_List_Tot_Base.op_At ts [t1]))
                      with
                      | (FStar_Reflection_Data.Tv_FVar fv,
                         (a1, FStar_Reflection_Data.Q_Implicit)::(a2,
                                                                  FStar_Reflection_Data.Q_Explicit)::
                         (a3, FStar_Reflection_Data.Q_Explicit)::[]) ->
                          (fun s ->
                             FStar_Tactics_Result.Success
                               ((if
                                   (FStar_Reflection_Builtins.inspect_fv fv)
                                     = FStar_Reflection_Const.eq2_qn
                                 then
                                   Comp
                                     ((Eq (FStar_Pervasives_Native.Some a1)),
                                       a2, a3)
                                 else
                                   if
                                     (FStar_Reflection_Builtins.inspect_fv fv)
                                       = FStar_Reflection_Const.eq1_qn
                                   then
                                     Comp
                                       ((BoolEq
                                           (FStar_Pervasives_Native.Some a1)),
                                         a2, a3)
                                   else
                                     if
                                       (FStar_Reflection_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.lt_qn
                                     then Comp (Lt, a2, a3)
                                     else
                                       if
                                         (FStar_Reflection_Builtins.inspect_fv
                                            fv)
                                           = FStar_Reflection_Const.lte_qn
                                       then Comp (Le, a2, a3)
                                       else
                                         if
                                           (FStar_Reflection_Builtins.inspect_fv
                                              fv)
                                             = FStar_Reflection_Const.gt_qn
                                         then Comp (Gt, a2, a3)
                                         else
                                           if
                                             (FStar_Reflection_Builtins.inspect_fv
                                                fv)
                                               =
                                               FStar_Reflection_Const.gte_qn
                                           then Comp (Ge, a2, a3)
                                           else
                                             App
                                               (h0,
                                                 (FStar_Pervasives_Native.fst
                                                    t1))), s))
                      | (FStar_Reflection_Data.Tv_FVar fv,
                         (a1, FStar_Reflection_Data.Q_Explicit)::(a2,
                                                                  FStar_Reflection_Data.Q_Explicit)::[])
                          ->
                          (fun s ->
                             FStar_Tactics_Result.Success
                               ((if
                                   (FStar_Reflection_Builtins.inspect_fv fv)
                                     = FStar_Reflection_Const.imp_qn
                                 then Implies (a1, a2)
                                 else
                                   if
                                     (FStar_Reflection_Builtins.inspect_fv fv)
                                       = FStar_Reflection_Const.and_qn
                                   then And (a1, a2)
                                   else
                                     if
                                       (FStar_Reflection_Builtins.inspect_fv
                                          fv)
                                         = FStar_Reflection_Const.iff_qn
                                     then Iff (a1, a2)
                                     else
                                       if
                                         (FStar_Reflection_Builtins.inspect_fv
                                            fv)
                                           = FStar_Reflection_Const.or_qn
                                       then Or (a1, a2)
                                       else
                                         if
                                           (FStar_Reflection_Builtins.inspect_fv
                                              fv)
                                             = FStar_Reflection_Const.eq2_qn
                                         then
                                           Comp
                                             ((Eq
                                                 FStar_Pervasives_Native.None),
                                               a1, a2)
                                         else
                                           if
                                             (FStar_Reflection_Builtins.inspect_fv
                                                fv)
                                               =
                                               FStar_Reflection_Const.eq1_qn
                                           then
                                             Comp
                                               ((BoolEq
                                                   FStar_Pervasives_Native.None),
                                                 a1, a2)
                                           else
                                             App
                                               (h0,
                                                 (FStar_Pervasives_Native.fst
                                                    t1))), s))
                      | (FStar_Reflection_Data.Tv_FVar fv,
                         (a1, FStar_Reflection_Data.Q_Implicit)::(a2,
                                                                  FStar_Reflection_Data.Q_Explicit)::[])
                          ->
                          (fun ps1 ->
                             match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Reflection.Formula.fst"
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (34))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Reflection.Formula.fst"
                                              (Prims.of_int (103))
                                              (Prims.of_int (17))
                                              (Prims.of_int (105))
                                              (Prims.of_int (31)))))
                             with
                             | true ->
                                 (if
                                    (FStar_Reflection_Builtins.inspect_fv fv)
                                      = FStar_Reflection_Const.forall_qn
                                  then mk_Forall a1 a2
                                  else
                                    if
                                      (FStar_Reflection_Builtins.inspect_fv
                                         fv)
                                        = FStar_Reflection_Const.exists_qn
                                    then mk_Exists a1 a2
                                    else
                                      (fun s ->
                                         FStar_Tactics_Result.Success
                                           ((App
                                               (h0,
                                                 (FStar_Pervasives_Native.fst
                                                    t1))), s)))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Reflection.Formula.fst"
                                                     (Prims.of_int (102))
                                                     (Prims.of_int (21))
                                                     (Prims.of_int (102))
                                                     (Prims.of_int (34))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Reflection.Formula.fst"
                                               (Prims.of_int (103))
                                               (Prims.of_int (17))
                                               (Prims.of_int (105))
                                               (Prims.of_int (31)))))))
                      | (FStar_Reflection_Data.Tv_FVar fv,
                         (a, FStar_Reflection_Data.Q_Explicit)::[]) ->
                          (fun s ->
                             FStar_Tactics_Result.Success
                               ((if
                                   (FStar_Reflection_Builtins.inspect_fv fv)
                                     = FStar_Reflection_Const.not_qn
                                 then Not a
                                 else
                                   App (h0, (FStar_Pervasives_Native.fst t1))),
                                 s))
                      | uu___ ->
                          (fun s ->
                             FStar_Tactics_Result.Success
                               ((App (h0, (FStar_Pervasives_Native.fst t1))),
                                 s)))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Reflection.Formula.fst"
                                   (Prims.of_int (79)) (Prims.of_int (22))
                                   (Prims.of_int (79)) (Prims.of_int (36))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Reflection.Formula.fst"
                             (Prims.of_int (79)) (Prims.of_int (8))
                             (Prims.of_int (111)) (Prims.of_int (26)))))))
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i) ->
        (fun s -> FStar_Tactics_Result.Success ((IntLit i), s))
    | FStar_Reflection_Data.Tv_Type uu___ ->
        (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
    | FStar_Reflection_Data.Tv_Abs (uu___, uu___1) ->
        (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
    | FStar_Reflection_Data.Tv_Refine (uu___, uu___1) ->
        (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Unit) ->
        (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
    | uu___ -> (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
let rec (is_name_imp :
  FStar_Reflection_Types.name -> FStar_Reflection_Types.term -> Prims.bool) =
  fun nm ->
    fun t ->
      match FStar_Reflection_Builtins.inspect_ln t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          if (FStar_Reflection_Builtins.inspect_fv fv) = nm
          then true
          else false
      | FStar_Reflection_Data.Tv_App
          (l, (uu___, FStar_Reflection_Data.Q_Implicit)) -> is_name_imp nm l
      | uu___ -> false
let (unsquash :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_App (l, (r, FStar_Reflection_Data.Q_Explicit))
        ->
        if is_name_imp FStar_Reflection_Const.squash_qn l
        then FStar_Pervasives_Native.Some r
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (unsquash_total :
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_App (l, (r, FStar_Reflection_Data.Q_Explicit))
        -> if is_name_imp FStar_Reflection_Const.squash_qn l then r else t
    | uu___ -> t
let (term_as_formula :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> formula FStar_Tactics_Result.__result)
  =
  fun t ->
    match unsquash t with
    | FStar_Pervasives_Native.None ->
        (fun s -> FStar_Tactics_Result.Success (F_Unknown, s))
    | FStar_Pervasives_Native.Some t1 -> term_as_formula' t1
let (term_as_formula_total :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> formula FStar_Tactics_Result.__result)
  = fun t -> term_as_formula' (unsquash_total t)
let (formula_as_term_view : formula -> FStar_Reflection_Data.term_view) =
  fun f ->
    let mk_app' tv args =
      FStar_List_Tot_Base.fold_left
        (fun tv1 ->
           fun a ->
             FStar_Reflection_Data.Tv_App
               ((FStar_Reflection_Builtins.pack_ln tv1), a)) tv args in
    let e = FStar_Reflection_Data.Q_Explicit in
    let i = FStar_Reflection_Data.Q_Implicit in
    match f with
    | True_ ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.true_qn)
    | False_ ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.false_qn)
    | Comp (Eq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn))
          [(l, e); (r, e)]
    | Comp (Eq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn))
          [(t, i); (l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq1_qn))
          [(l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq1_qn))
          [(t, i); (l, e); (r, e)]
    | Comp (Lt, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.lt_qn))
          [(l, e); (r, e)]
    | Comp (Le, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.lte_qn))
          [(l, e); (r, e)]
    | Comp (Gt, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.gt_qn))
          [(l, e); (r, e)]
    | Comp (Ge, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.gte_qn))
          [(l, e); (r, e)]
    | And (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.and_qn))
          [(p, e); (q, e)]
    | Or (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.or_qn))
          [(p, e); (q, e)]
    | Implies (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.imp_qn))
          [(p, e); (q, e)]
    | Not p ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.not_qn))
          [(p, e)]
    | Iff (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.iff_qn))
          [(p, e); (q, e)]
    | Forall (b, t) -> FStar_Reflection_Data.Tv_Unknown
    | Exists (b, t) -> FStar_Reflection_Data.Tv_Unknown
    | App (p, q) ->
        FStar_Reflection_Data.Tv_App
          (p, (q, FStar_Reflection_Data.Q_Explicit))
    | Name b -> FStar_Reflection_Data.Tv_Var b
    | FV fv -> FStar_Reflection_Data.Tv_FVar fv
    | IntLit i1 ->
        FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i1)
    | F_Unknown -> FStar_Reflection_Data.Tv_Unknown
let (formula_as_term : formula -> FStar_Reflection_Types.term) =
  fun f -> FStar_Reflection_Builtins.pack_ln (formula_as_term_view f)
let (formula_to_string : formula -> Prims.string) =
  fun f ->
    match f with
    | True_ -> "True_"
    | False_ -> "False_"
    | Comp (Eq mt, l, r) ->
        Prims.strcat "Eq"
          (Prims.strcat
             (match mt with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some t ->
                  Prims.strcat " ("
                    (Prims.strcat
                       (FStar_Reflection_Builtins.term_to_string t) ")"))
             (Prims.strcat " ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Builtins.term_to_string r) ")")))))
    | Comp (BoolEq mt, l, r) ->
        Prims.strcat "BoolEq"
          (Prims.strcat
             (match mt with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some t ->
                  Prims.strcat " ("
                    (Prims.strcat
                       (FStar_Reflection_Builtins.term_to_string t) ")"))
             (Prims.strcat " ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Builtins.term_to_string r) ")")))))
    | Comp (Lt, l, r) ->
        Prims.strcat "Lt ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string r)
                   ")")))
    | Comp (Le, l, r) ->
        Prims.strcat "Le ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string r)
                   ")")))
    | Comp (Gt, l, r) ->
        Prims.strcat "Gt ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string r)
                   ")")))
    | Comp (Ge, l, r) ->
        Prims.strcat "Ge ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string l)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string r)
                   ")")))
    | And (p, q) ->
        Prims.strcat "And ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string q)
                   ")")))
    | Or (p, q) ->
        Prims.strcat "Or ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string q)
                   ")")))
    | Implies (p, q) ->
        Prims.strcat "Implies ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string q)
                   ")")))
    | Not p ->
        Prims.strcat "Not ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p) ")")
    | Iff (p, q) ->
        Prims.strcat "Iff ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string q)
                   ")")))
    | Forall (bs, t) ->
        Prims.strcat "Forall <bs> ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string t) ")")
    | Exists (bs, t) ->
        Prims.strcat "Exists <bs> ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string t) ")")
    | App (p, q) ->
        Prims.strcat "App ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string q)
                   ")")))
    | Name bv ->
        Prims.strcat "Name ("
          (Prims.strcat (FStar_Reflection_Derived.bv_to_string bv) ")")
    | FV fv ->
        Prims.strcat "FV ("
          (Prims.strcat
             (FStar_Reflection_Derived.flatten_name
                (FStar_Reflection_Builtins.inspect_fv fv)) ")")
    | IntLit i -> Prims.strcat "Int " (Prims.string_of_int i)
    | F_Unknown -> "?"