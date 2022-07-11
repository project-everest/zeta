open Prims
let (name_of_bv : FStar_Reflection_Types.bv -> Prims.string) =
  fun bv ->
    (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_ppname
let (type_of_bv : FStar_Reflection_Types.bv -> FStar_Reflection_Types.typ) =
  fun bv ->
    (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_sort
let (bv_to_string : FStar_Reflection_Types.bv -> Prims.string) =
  fun bv ->
    let bvv = FStar_Reflection_Builtins.inspect_bv bv in
    Prims.strcat "("
      (Prims.strcat bvv.FStar_Reflection_Data.bv_ppname
         (Prims.strcat ":"
            (Prims.strcat
               (FStar_Reflection_Builtins.term_to_string
                  bvv.FStar_Reflection_Data.bv_sort) ")")))
let (bv_of_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.bv) =
  fun b ->
    let uu___ = FStar_Reflection_Builtins.inspect_binder b in
    match uu___ with | (bv, uu___1) -> bv
let (mk_binder : FStar_Reflection_Types.bv -> FStar_Reflection_Types.binder)
  =
  fun bv ->
    FStar_Reflection_Builtins.pack_binder bv FStar_Reflection_Data.Q_Explicit
      []
let (mk_implicit_binder :
  FStar_Reflection_Types.bv -> FStar_Reflection_Types.binder) =
  fun bv ->
    FStar_Reflection_Builtins.pack_binder bv FStar_Reflection_Data.Q_Implicit
      []
let (name_of_binder : FStar_Reflection_Types.binder -> Prims.string) =
  fun b -> name_of_bv (bv_of_binder b)
let (type_of_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.typ) =
  fun b -> type_of_bv (bv_of_binder b)
let (binder_to_string : FStar_Reflection_Types.binder -> Prims.string) =
  fun b -> bv_to_string (bv_of_binder b)
let rec (flatten_name : FStar_Reflection_Types.name -> Prims.string) =
  fun ns ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let rec (collect_app' :
  FStar_Reflection_Data.argv Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  =
  fun args ->
    fun t ->
      match FStar_Reflection_Builtins.inspect_ln t with
      | FStar_Reflection_Data.Tv_App (l, r) -> collect_app' (r :: args) l
      | uu___ -> (t, args)
let (collect_app :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  = collect_app' []
let rec (mk_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.argv Prims.list -> FStar_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_App (t, x))) xs
let (mk_e_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term)
  =
  fun t ->
    fun args ->
      let e t1 = (t1, FStar_Reflection_Data.Q_Explicit) in
      mk_app t (FStar_List_Tot_Base.map e args)
let rec (mk_tot_arr_ln :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> cod
      | b::bs1 ->
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Arrow
               (b,
                 (FStar_Reflection_Builtins.pack_comp
                    (FStar_Reflection_Data.C_Total
                       ((mk_tot_arr_ln bs1 cod), [])))))
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.comp))
  =
  fun bs ->
    fun c ->
      match FStar_Reflection_Builtins.inspect_comp c with
      | FStar_Reflection_Data.C_Total (t, uu___) ->
          (match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_Arrow (b, c1) ->
               collect_arr' (b :: bs) c1
           | uu___1 -> (bs, c))
      | uu___ -> (bs, c)
let (collect_arr_ln_bs :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStar_Reflection_Builtins.pack_comp
           (FStar_Reflection_Data.C_Total (t, []))) in
    match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)
let (collect_arr_ln :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp))
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStar_Reflection_Builtins.pack_comp
           (FStar_Reflection_Data.C_Total (t, []))) in
    match uu___ with
    | (bs, c) ->
        let ts = FStar_List_Tot_Base.map type_of_binder bs in
        ((FStar_List_Tot_Base.rev ts), c)
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match FStar_Reflection_Builtins.inspect_ln t with
      | FStar_Reflection_Data.Tv_Abs (b, t') -> collect_abs' (b :: bs) t'
      | uu___ -> (bs, t)
let (collect_abs_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term))
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    match uu___ with | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')
let (fv_to_string : FStar_Reflection_Types.fv -> Prims.string) =
  fun fv ->
    FStar_Reflection_Builtins.implode_qn
      (FStar_Reflection_Builtins.inspect_fv fv)
let (compare_name :
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.name -> FStar_Order.order)
  =
  fun n1 ->
    fun n2 ->
      FStar_Order.compare_list
        (fun s1 ->
           fun s2 ->
             FStar_Order.order_from_int
               (FStar_Reflection_Builtins.compare_string s1 s2)) n1 n2
let (compare_fv :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> FStar_Order.order)
  =
  fun f1 ->
    fun f2 ->
      compare_name (FStar_Reflection_Builtins.inspect_fv f1)
        (FStar_Reflection_Builtins.inspect_fv f2)
let (compare_const :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Data.vconst -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStar_Reflection_Data.C_Unit, FStar_Reflection_Data.C_Unit) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Int i, FStar_Reflection_Data.C_Int j) ->
          FStar_Order.order_from_int (i - j)
      | (FStar_Reflection_Data.C_True, FStar_Reflection_Data.C_True) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_False, FStar_Reflection_Data.C_False) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_String s1, FStar_Reflection_Data.C_String
         s2) ->
          FStar_Order.order_from_int
            (FStar_Reflection_Builtins.compare_string s1 s2)
      | (FStar_Reflection_Data.C_Range r1, FStar_Reflection_Data.C_Range r2)
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reify, FStar_Reflection_Data.C_Reify) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reflect l1, FStar_Reflection_Data.C_Reflect
         l2) -> compare_name l1 l2
      | (FStar_Reflection_Data.C_Unit, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Unit) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Int uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Int uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_True, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_True) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_False, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_False) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_String uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_String uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Range uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Range uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reify, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Reify) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reflect uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Reflect uu___1) -> FStar_Order.Gt
let (compare_binder :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.binder -> FStar_Order.order)
  =
  fun b1 ->
    fun b2 ->
      let uu___ = FStar_Reflection_Builtins.inspect_binder b1 in
      match uu___ with
      | (bv1, uu___1) ->
          let uu___2 = FStar_Reflection_Builtins.inspect_binder b2 in
          (match uu___2 with
           | (bv2, uu___3) -> FStar_Reflection_Builtins.compare_bv bv1 bv2)
let rec (compare_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Order.order)
  =
  fun s ->
    fun t ->
      match ((FStar_Reflection_Builtins.inspect_ln s),
              (FStar_Reflection_Builtins.inspect_ln t))
      with
      | (FStar_Reflection_Data.Tv_Var sv, FStar_Reflection_Data.Tv_Var tv) ->
          FStar_Reflection_Builtins.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_BVar sv, FStar_Reflection_Data.Tv_BVar tv)
          -> FStar_Reflection_Builtins.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_FVar sv, FStar_Reflection_Data.Tv_FVar tv)
          -> compare_fv sv tv
      | (FStar_Reflection_Data.Tv_App (h1, a1), FStar_Reflection_Data.Tv_App
         (h2, a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu___ -> compare_argv a1 a2)
      | (FStar_Reflection_Data.Tv_Abs (b1, e1), FStar_Reflection_Data.Tv_Abs
         (b2, e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu___ -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Refine (bv1, e1),
         FStar_Reflection_Data.Tv_Refine (bv2, e2)) ->
          FStar_Order.lex (FStar_Reflection_Builtins.compare_bv bv1 bv2)
            (fun uu___ -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Arrow (b1, e1),
         FStar_Reflection_Data.Tv_Arrow (b2, e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu___ -> compare_comp e1 e2)
      | (FStar_Reflection_Data.Tv_Type (), FStar_Reflection_Data.Tv_Type ())
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Const c1, FStar_Reflection_Data.Tv_Const
         c2) -> compare_const c1 c2
      | (FStar_Reflection_Data.Tv_Uvar (u1, uu___),
         FStar_Reflection_Data.Tv_Uvar (u2, uu___1)) ->
          FStar_Order.compare_int u1 u2
      | (FStar_Reflection_Data.Tv_Let (_r1, _attrs1, bv1, t1, t1'),
         FStar_Reflection_Data.Tv_Let (_r2, _attrs2, bv2, t2, t2')) ->
          FStar_Order.lex (FStar_Reflection_Builtins.compare_bv bv1 bv2)
            (fun uu___ ->
               FStar_Order.lex (compare_term t1 t2)
                 (fun uu___1 -> compare_term t1' t2'))
      | (FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2),
         FStar_Reflection_Data.Tv_Match (uu___3, uu___4, uu___5)) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_AscribedT (e1, t1, tac1),
         FStar_Reflection_Data.Tv_AscribedT (e2, t2, tac2)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu___ ->
               FStar_Order.lex (compare_term t1 t2)
                 (fun uu___1 ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None, uu___2) ->
                        FStar_Order.Lt
                    | (uu___2, FStar_Pervasives_Native.None) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some e11,
                       FStar_Pervasives_Native.Some e21) ->
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_AscribedC (e1, c1, tac1),
         FStar_Reflection_Data.Tv_AscribedC (e2, c2, tac2)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu___ ->
               FStar_Order.lex (compare_comp c1 c2)
                 (fun uu___1 ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None, uu___2) ->
                        FStar_Order.Lt
                    | (uu___2, FStar_Pervasives_Native.None) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some e11,
                       FStar_Pervasives_Native.Some e21) ->
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_Unknown, FStar_Reflection_Data.Tv_Unknown)
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Var uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Var uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_BVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_BVar uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_FVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_FVar uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_App (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_App (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Abs (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Abs (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Arrow (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Arrow (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Type (), uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Type ()) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Refine (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Refine (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Const uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Const uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Uvar (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Uvar (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2), uu___3) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Match (uu___1, uu___2, uu___3)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedT (uu___, uu___1, uu___2), uu___3)
          -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_AscribedT (uu___1, uu___2, uu___3))
          -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedC (uu___, uu___1, uu___2), uu___3)
          -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_AscribedC (uu___1, uu___2, uu___3))
          -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Unknown, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Unknown) -> FStar_Order.Gt
and (compare_term_list :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term Prims.list -> FStar_Order.order)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> FStar_Order.Eq
      | ([], uu___) -> FStar_Order.Lt
      | (uu___, []) -> FStar_Order.Gt
      | (hd1::tl1, hd2::tl2) ->
          FStar_Order.lex (compare_term hd1 hd2)
            (fun uu___ -> compare_term_list tl1 tl2)
and (compare_argv :
  FStar_Reflection_Data.argv ->
    FStar_Reflection_Data.argv -> FStar_Order.order)
  =
  fun a1 ->
    fun a2 ->
      let uu___ = a1 in
      match uu___ with
      | (a11, q1) ->
          let uu___1 = a2 in
          (match uu___1 with
           | (a21, q2) ->
               (match (q1, q2) with
                | (FStar_Reflection_Data.Q_Implicit,
                   FStar_Reflection_Data.Q_Explicit) -> FStar_Order.Lt
                | (FStar_Reflection_Data.Q_Explicit,
                   FStar_Reflection_Data.Q_Implicit) -> FStar_Order.Gt
                | (uu___2, uu___3) -> compare_term a11 a21))
and (compare_comp :
  FStar_Reflection_Types.comp ->
    FStar_Reflection_Types.comp -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      let cv1 = FStar_Reflection_Builtins.inspect_comp c1 in
      let cv2 = FStar_Reflection_Builtins.inspect_comp c2 in
      match (cv1, cv2) with
      | (FStar_Reflection_Data.C_Total (t1, md1),
         FStar_Reflection_Data.C_Total (t2, md2)) ->
          FStar_Order.lex (compare_term t1 t2)
            (fun uu___ -> compare_term_list md1 md2)
      | (FStar_Reflection_Data.C_GTotal (t1, md1),
         FStar_Reflection_Data.C_GTotal (t2, md2)) ->
          FStar_Order.lex (compare_term t1 t2)
            (fun uu___ -> compare_term_list md1 md2)
      | (FStar_Reflection_Data.C_Lemma (p1, q1, s1),
         FStar_Reflection_Data.C_Lemma (p2, q2, s2)) ->
          FStar_Order.lex (compare_term p1 p2)
            (fun uu___ ->
               FStar_Order.lex (compare_term q1 q2)
                 (fun uu___1 -> compare_term s1 s2))
      | (FStar_Reflection_Data.C_Eff (_us1, eff1, res1, args1),
         FStar_Reflection_Data.C_Eff (_us2, eff2, res2, args2)) ->
          FStar_Order.lex (compare_name eff1 eff2)
            (fun uu___ -> compare_term res1 res2)
      | (FStar_Reflection_Data.C_Total (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Total (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_GTotal (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_GTotal (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Lemma (uu___, uu___1, uu___2), uu___3) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Lemma (uu___1, uu___2, uu___3)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Eff (uu___, uu___1, uu___2, uu___3), uu___4)
          -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Eff (uu___1, uu___2, uu___3, uu___4))
          -> FStar_Order.Gt
let (mk_stringlit : Prims.string -> FStar_Reflection_Types.term) =
  fun s ->
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_String s))
let (mk_strcat :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      mk_e_app
        (FStar_Reflection_Builtins.pack_ln
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Builtins.pack_fv ["Prims"; "strcat"])))
        [t1; t2]
let (mk_cons :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun h ->
    fun t ->
      mk_e_app
        (FStar_Reflection_Builtins.pack_ln
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Builtins.pack_fv
                 FStar_Reflection_Const.cons_qn))) [h; t]
let (mk_cons_t :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun h ->
      fun t ->
        mk_app
          (FStar_Reflection_Builtins.pack_ln
             (FStar_Reflection_Data.Tv_FVar
                (FStar_Reflection_Builtins.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, FStar_Reflection_Data.Q_Implicit);
          (h, FStar_Reflection_Data.Q_Explicit);
          (t, FStar_Reflection_Data.Q_Explicit)]
let rec (mk_list :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts ->
    match ts with
    | [] ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.nil_qn))
    | t::ts1 -> mk_cons t (mk_list ts1)
let (mktuple_n :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts ->
    match FStar_List_Tot_Base.length ts with
    | uu___ when uu___ = Prims.int_zero ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit)
    | uu___ when uu___ = Prims.int_one ->
        let uu___1 = ts in (match uu___1 with | x::[] -> x)
    | n ->
        let qn =
          match n with
          | uu___ when uu___ = (Prims.of_int (2)) ->
              FStar_Reflection_Const.mktuple2_qn
          | uu___ when uu___ = (Prims.of_int (3)) ->
              FStar_Reflection_Const.mktuple3_qn
          | uu___ when uu___ = (Prims.of_int (4)) ->
              FStar_Reflection_Const.mktuple4_qn
          | uu___ when uu___ = (Prims.of_int (5)) ->
              FStar_Reflection_Const.mktuple5_qn
          | uu___ when uu___ = (Prims.of_int (6)) ->
              FStar_Reflection_Const.mktuple6_qn
          | uu___ when uu___ = (Prims.of_int (7)) ->
              FStar_Reflection_Const.mktuple7_qn
          | uu___ when uu___ = (Prims.of_int (8)) ->
              FStar_Reflection_Const.mktuple8_qn in
        mk_e_app
          (FStar_Reflection_Builtins.pack_ln
             (FStar_Reflection_Data.Tv_FVar
                (FStar_Reflection_Builtins.pack_fv qn))) ts
let (destruct_tuple :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = collect_app t in
    match uu___ with
    | (head, args) ->
        (match FStar_Reflection_Builtins.inspect_ln head with
         | FStar_Reflection_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem
                 (FStar_Reflection_Builtins.inspect_fv fv)
                 [FStar_Reflection_Const.mktuple2_qn;
                 FStar_Reflection_Const.mktuple3_qn;
                 FStar_Reflection_Const.mktuple4_qn;
                 FStar_Reflection_Const.mktuple5_qn;
                 FStar_Reflection_Const.mktuple6_qn;
                 FStar_Reflection_Const.mktuple7_qn;
                 FStar_Reflection_Const.mktuple8_qn]
             then
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.concatMap
                    (fun uu___1 ->
                       match uu___1 with
                       | (t1, q) ->
                           (match q with
                            | FStar_Reflection_Data.Q_Explicit -> [t1]
                            | uu___2 -> [])) args)
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (mkpair :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun t1 -> fun t2 -> mktuple_n [t1; t2]
let rec (head : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_Match (t1, uu___, uu___1) -> head t1
    | FStar_Reflection_Data.Tv_Let (uu___, uu___1, uu___2, t1, uu___3) ->
        head t1
    | FStar_Reflection_Data.Tv_Abs (uu___, t1) -> head t1
    | FStar_Reflection_Data.Tv_Refine (uu___, t1) -> head t1
    | FStar_Reflection_Data.Tv_App (t1, uu___) -> head t1
    | FStar_Reflection_Data.Tv_AscribedT (t1, uu___, uu___1) -> head t1
    | FStar_Reflection_Data.Tv_AscribedC (t1, uu___, uu___1) -> head t1
    | FStar_Reflection_Data.Tv_Unknown -> t
    | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) -> t
    | FStar_Reflection_Data.Tv_Const uu___ -> t
    | FStar_Reflection_Data.Tv_Type uu___ -> t
    | FStar_Reflection_Data.Tv_Var uu___ -> t
    | FStar_Reflection_Data.Tv_BVar uu___ -> t
    | FStar_Reflection_Data.Tv_FVar uu___ -> t
    | FStar_Reflection_Data.Tv_Arrow (uu___, uu___1) -> t
let (nameof : FStar_Reflection_Types.term -> Prims.string) =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        FStar_Reflection_Builtins.implode_qn
          (FStar_Reflection_Builtins.inspect_fv fv)
    | uu___ -> "?"
let (is_uvar : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln (head t) with
    | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) -> true
    | uu___ -> false
let (binder_set_qual :
  FStar_Reflection_Data.aqualv ->
    FStar_Reflection_Types.binder -> FStar_Reflection_Types.binder)
  =
  fun q ->
    fun b ->
      let uu___ = FStar_Reflection_Builtins.inspect_binder b in
      match uu___ with
      | (bv, (uu___1, attrs)) ->
          FStar_Reflection_Builtins.pack_binder bv q attrs
let (add_check_with :
  FStar_VConfig.vconfig ->
    FStar_Reflection_Types.sigelt -> FStar_Reflection_Types.sigelt)
  =
  fun vcfg ->
    fun se ->
      let attrs = FStar_Reflection_Builtins.sigelt_attrs se in
      let vcfg_t = FStar_Reflection_Builtins.embed_vconfig vcfg in
      let t =
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["FStar"; "Reflection"; "Builtins"; "check_with"]))),
               (vcfg_t, FStar_Reflection_Data.Q_Explicit))) in
      FStar_Reflection_Builtins.set_sigelt_attrs (t :: attrs) se