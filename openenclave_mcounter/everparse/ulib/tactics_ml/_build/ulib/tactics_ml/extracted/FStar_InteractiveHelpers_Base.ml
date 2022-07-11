open Prims
let (bv_eq :
  FStar_Reflection_Types.bv -> FStar_Reflection_Types.bv -> Prims.bool) =
  fun bv1 ->
    fun bv2 ->
      let bvv1 = FStar_Reflection_Builtins.inspect_bv bv1 in
      let bvv2 = FStar_Reflection_Builtins.inspect_bv bv2 in
      (bvv1.FStar_Reflection_Data.bv_ppname =
         bvv2.FStar_Reflection_Data.bv_ppname)
        &&
        (bvv1.FStar_Reflection_Data.bv_index =
           bvv2.FStar_Reflection_Data.bv_index)
let (fv_eq :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 ->
      let n1 = FStar_Reflection_Builtins.inspect_fv fv1 in
      let n2 = FStar_Reflection_Builtins.inspect_fv fv2 in n1 = n2
let (fv_eq_name :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.name -> Prims.bool) =
  fun fv ->
    fun n -> let fvn = FStar_Reflection_Builtins.inspect_fv fv in fvn = n
let opt_apply :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x' ->
          FStar_Pervasives_Native.Some (f x')
let opt_tapply :
  'a 'b .
    ('a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a FStar_Pervasives_Native.option ->
        FStar_Tactics_Types.proofstate ->
          'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None ->
          (fun s ->
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
      | FStar_Pervasives_Native.Some x' ->
          (fun ps ->
             match (f x')
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (42)) (Prims.of_int (20))
                                 (Prims.of_int (42)) (Prims.of_int (26))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (42)) (Prims.of_int (15))
                                   (Prims.of_int (42)) (Prims.of_int (26)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Pervasives_Native.Some a1),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (42)) (Prims.of_int (15))
                                      (Prims.of_int (42)) (Prims.of_int (26))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let option_to_string :
  'a .
    ('a -> Prims.string) -> 'a FStar_Pervasives_Native.option -> Prims.string
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x' ->
          Prims.strcat "Some (" (Prims.strcat (f x') ")")
let opt_cons :
  'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list -> 'a Prims.list =
  fun opt_x ->
    fun ls ->
      match opt_x with
      | FStar_Pervasives_Native.Some x -> x :: ls
      | FStar_Pervasives_Native.None -> ls
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun ls ->
      Prims.strcat
        (FStar_List_Tot_Base.fold_left
           (fun s ->
              fun x ->
                Prims.strcat s (Prims.strcat " (" (Prims.strcat (f x) ");")))
           "[" ls) "]"
let (mk_app_norm :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      fun params ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (65)) (Prims.of_int (11))
                                 (Prims.of_int (65)) (Prims.of_int (28))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (66)) (Prims.of_int (2))
                           (Prims.of_int (67)) (Prims.of_int (4)))))
          with
          | true ->
              (match (FStar_Tactics_Builtins.norm_term_env e []
                        (FStar_Reflection_Derived.mk_e_app t params))
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (65))
                                               (Prims.of_int (11))
                                               (Prims.of_int (65))
                                               (Prims.of_int (28))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                         (Prims.of_int (66))
                                         (Prims.of_int (2))
                                         (Prims.of_int (67))
                                         (Prims.of_int (4))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (66)) (Prims.of_int (11))
                                   (Prims.of_int (66)) (Prims.of_int (32))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (66)) (Prims.of_int (6))
                                     (Prims.of_int (66)) (Prims.of_int (8)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          (a,
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (66))
                                        (Prims.of_int (6))
                                        (Prims.of_int (66))
                                        (Prims.of_int (8))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
let (opt_mk_app_norm :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
      FStar_Reflection_Types.term Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun opt_t ->
      fun params -> opt_tapply (fun t -> mk_app_norm e t params) opt_t
let rec unzip :
  'a 'b . ('a * 'b) Prims.list -> ('a Prims.list * 'b Prims.list) =
  fun l ->
    match l with
    | [] -> ([], [])
    | (hd1, hd2)::tl ->
        let uu___ = unzip tl in
        (match uu___ with | (tl1, tl2) -> ((hd1 :: tl1), (hd2 :: tl2)))
let (abv_to_string : FStar_Reflection_Types.bv -> Prims.string) =
  fun bv ->
    let bvv = FStar_Reflection_Builtins.inspect_bv bv in
    Prims.strcat bvv.FStar_Reflection_Data.bv_ppname
      (Prims.strcat " (%"
         (Prims.strcat
            (Prims.string_of_int bvv.FStar_Reflection_Data.bv_index)
            (Prims.strcat ") : "
               (FStar_Reflection_Builtins.term_to_string
                  bvv.FStar_Reflection_Data.bv_sort))))
let (print_binder_info :
  Prims.bool ->
    FStar_Reflection_Types.binder ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun full ->
    fun b ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.Base.fst"
                               (Prims.of_int (89)) (Prims.of_int (24))
                               (Prims.of_int (89)) (Prims.of_int (40))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range
                         "experimental/FStar.InteractiveHelpers.Base.fst"
                         (Prims.of_int (89)) (Prims.of_int (2))
                         (Prims.of_int (107)) (Prims.of_int (33)))))
        with
        | true ->
            ((match FStar_Reflection_Builtins.inspect_binder b with
              | (bv, (a, _attrs)) ->
                  (fun ps1 ->
                     match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (90))
                                            (Prims.of_int (14))
                                            (Prims.of_int (93))
                                            (Prims.of_int (45))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (96)) (Prims.of_int (2))
                                      (Prims.of_int (107))
                                      (Prims.of_int (33)))))
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
                                                       ps1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (90))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (93))
                                                             (Prims.of_int (45))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                                       (Prims.of_int (96))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (107))
                                                       (Prims.of_int (33))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (96))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (96))
                                                 (Prims.of_int (27))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.Base.fst"
                                           (Prims.of_int (97))
                                           (Prims.of_int (2))
                                           (Prims.of_int (107))
                                           (Prims.of_int (33)))))
                          with
                          | true ->
                              (if full
                               then
                                 FStar_Tactics_Builtins.print
                                   (Prims.strcat "> print_binder_info:"
                                      (Prims.strcat "\n- name: "
                                         (Prims.strcat
                                            (FStar_Reflection_Derived.name_of_binder
                                               b)
                                            (Prims.strcat "\n- as string: "
                                               (Prims.strcat
                                                  (FStar_Reflection_Derived.binder_to_string
                                                     b)
                                                  (Prims.strcat "\n- aqual: "
                                                     (Prims.strcat
                                                        (match a with
                                                         | FStar_Reflection_Data.Q_Implicit
                                                             -> "Implicit"
                                                         | FStar_Reflection_Data.Q_Explicit
                                                             -> "Explicit"
                                                         | FStar_Reflection_Data.Q_Meta
                                                             t ->
                                                             Prims.strcat
                                                               "Meta: "
                                                               (FStar_Reflection_Builtins.term_to_string
                                                                  t))
                                                        (Prims.strcat
                                                           "\n- ppname: "
                                                           (Prims.strcat
                                                              (FStar_Reflection_Builtins.inspect_bv
                                                                 bv).FStar_Reflection_Data.bv_ppname
                                                              (Prims.strcat
                                                                 "\n- index: "
                                                                 (Prims.strcat
                                                                    (
                                                                    Prims.string_of_int
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_index)
                                                                    (
                                                                    Prims.strcat
                                                                    "\n- sort: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_sort)))))))))))))
                               else
                                 FStar_Tactics_Builtins.print
                                   (FStar_Reflection_Derived.binder_to_string
                                      b))
                                (FStar_Tactics_Types.decr_depth
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
                                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                                              (Prims.of_int (90))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (93))
                                                              (Prims.of_int (45))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (96))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (107))
                                                        (Prims.of_int (33))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (96))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (96))
                                                  (Prims.of_int (27))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (97))
                                            (Prims.of_int (2))
                                            (Prims.of_int (107))
                                            (Prims.of_int (33))))))))))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (89)) (Prims.of_int (24))
                                (Prims.of_int (89)) (Prims.of_int (40))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (89)) (Prims.of_int (2))
                          (Prims.of_int (107)) (Prims.of_int (33))))))
let (print_binders_info :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun full ->
    fun e ->
      FStar_Tactics_Util.iter (print_binder_info full)
        (FStar_Reflection_Builtins.binders_of_env e)
let (acomp_to_string : FStar_Reflection_Types.comp -> Prims.string) =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total (ret, decr) ->
        Prims.strcat "C_Total ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string ret) ")")
    | FStar_Reflection_Data.C_GTotal (ret, decr) ->
        Prims.strcat "C_GTotal ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string ret) ")")
    | FStar_Reflection_Data.C_Lemma (pre, post, patterns) ->
        Prims.strcat "C_Lemma ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string pre)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Builtins.term_to_string post)
                   ")")))
    | FStar_Reflection_Data.C_Eff (us, eff_name, result, eff_args) ->
        let eff_arg_to_string a =
          Prims.strcat " ("
            (Prims.strcat (FStar_Reflection_Builtins.term_to_string a) ")") in
        let args_str =
          FStar_List_Tot_Base.map
            (fun uu___ -> match uu___ with | (x, y) -> eff_arg_to_string x)
            eff_args in
        let args_str1 =
          FStar_List_Tot_Base.fold_left (fun x -> fun y -> Prims.strcat x y)
            "" args_str in
        Prims.strcat "C_Eff ("
          (Prims.strcat (FStar_Reflection_Derived.flatten_name eff_name)
             (Prims.strcat ") ("
                (Prims.strcat
                   (FStar_Reflection_Builtins.term_to_string result)
                   (Prims.strcat ")" args_str1))))
exception MetaAnalysis of Prims.string 
let (uu___is_MetaAnalysis : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MetaAnalysis uu___ -> true | uu___ -> false
let (__proj__MetaAnalysis__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MetaAnalysis uu___ -> uu___
let mfail :
  'uuuuu .
    Prims.string ->
      FStar_Tactics_Types.proofstate -> 'uuuuu FStar_Tactics_Result.__result
  = fun str -> FStar_Tactics_Effect.raise (MetaAnalysis str)
let (print_dbg :
  Prims.bool ->
    Prims.string ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun debug ->
    fun s ->
      if debug
      then FStar_Tactics_Builtins.print s
      else (fun s1 -> FStar_Tactics_Result.Success ((), s1))
let (term_view_construct :
  FStar_Reflection_Data.term_view ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun t ->
    fun s ->
      FStar_Tactics_Result.Success
        ((match t with
          | FStar_Reflection_Data.Tv_Var uu___ -> "Tv_Var"
          | FStar_Reflection_Data.Tv_BVar uu___ -> "Tv_BVar"
          | FStar_Reflection_Data.Tv_FVar uu___ -> "Tv_FVar"
          | FStar_Reflection_Data.Tv_App (uu___, uu___1) -> "Tv_App"
          | FStar_Reflection_Data.Tv_Abs (uu___, uu___1) -> "Tv_Abs"
          | FStar_Reflection_Data.Tv_Arrow (uu___, uu___1) -> "Tv_Arrow"
          | FStar_Reflection_Data.Tv_Type uu___ -> "Tv_Type"
          | FStar_Reflection_Data.Tv_Refine (uu___, uu___1) -> "Tv_Refine"
          | FStar_Reflection_Data.Tv_Const uu___ -> "Tv_Const"
          | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) -> "Tv_Uvar"
          | FStar_Reflection_Data.Tv_Let
              (uu___, uu___1, uu___2, uu___3, uu___4) -> "Tv_Let"
          | FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2) ->
              "Tv_Match"
          | FStar_Reflection_Data.Tv_AscribedT (uu___, uu___1, uu___2) ->
              "Tv_AscribedT"
          | FStar_Reflection_Data.Tv_AscribedC (uu___, uu___1, uu___2) ->
              "Tv_AScribedC"
          | uu___ -> "Tv_Unknown"), s)
let (term_construct :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (162)) (Prims.of_int (22))
                          (Prims.of_int (162)) (Prims.of_int (33))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (162)) (Prims.of_int (2))
                            (Prims.of_int (162)) (Prims.of_int (33)))))
           with
           | true ->
               (term_view_construct a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.Base.fst"
                             (Prims.of_int (162)) (Prims.of_int (2))
                             (Prims.of_int (162)) (Prims.of_int (33)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (filter_ascriptions :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun t ->
      fun ps ->
        match match match match match (FStar_Tactics_Builtins.inspect t)
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
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (94))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (94))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (175))
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (175))
                                                                (Prims.of_int (92))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (175))
                                                          (Prims.of_int (45))
                                                          (Prims.of_int (175))
                                                          (Prims.of_int (66))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (27))
                                                    (Prims.of_int (174))
                                                    (Prims.of_int (28))))))
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (175))
                                                      (Prims.of_int (45))
                                                      (Prims.of_int (175))
                                                      (Prims.of_int (66)))))
                                     with
                                     | true ->
                                         (term_view_construct a)
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                                       (Prims.of_int (175))
                                                       (Prims.of_int (45))
                                                       (Prims.of_int (175))
                                                       (Prims.of_int (66)))))))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range "prims.fst"
                                                (Prims.of_int (603))
                                                (Prims.of_int (19))
                                                (Prims.of_int (603))
                                                (Prims.of_int (31)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((Prims.strcat a
                                         (Prims.strcat ": "
                                            (FStar_Reflection_Builtins.term_to_string
                                               t))),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (603))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (603))
                                                   (Prims.of_int (31))))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps')
                    with
                    | FStar_Tactics_Result.Success (a, ps') ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range "prims.fst"
                                          (Prims.of_int (603))
                                          (Prims.of_int (19))
                                          (Prims.of_int (603))
                                          (Prims.of_int (31)))))
                         with
                         | true ->
                             FStar_Tactics_Result.Success
                               ((Prims.strcat "[> filter_ascriptions: " a),
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (603))
                                             (Prims.of_int (19))
                                             (Prims.of_int (603))
                                             (Prims.of_int (31))))))))
                    | FStar_Tactics_Result.Failed (e, ps') ->
                        FStar_Tactics_Result.Failed (e, ps')
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (175)) (Prims.of_int (2))
                                    (Prims.of_int (175)) (Prims.of_int (94)))))
                   with
                   | true ->
                       (print_dbg dbg a)
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (175)) (Prims.of_int (2))
                                     (Prims.of_int (175)) (Prims.of_int (94)))))))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (176)) (Prims.of_int (2))
                              (Prims.of_int (180)) (Prims.of_int (15)))))
             with
             | true ->
                 (FStar_Tactics_Derived.visit_tm
                    (fun t1 ->
                       fun ps1 ->
                         match (FStar_Tactics_Builtins.inspect t1)
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (177))
                                             (Prims.of_int (10))
                                             (Prims.of_int (177))
                                             (Prims.of_int (19))))))
                         with
                         | FStar_Tactics_Result.Success (a1, ps'1) ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (177))
                                               (Prims.of_int (4))
                                               (Prims.of_int (180))
                                               (Prims.of_int (12)))))
                              with
                              | true ->
                                  ((match a1 with
                                    | FStar_Reflection_Data.Tv_AscribedT
                                        (e, uu___, uu___1) ->
                                        (fun s ->
                                           FStar_Tactics_Result.Success
                                             (e, s))
                                    | FStar_Reflection_Data.Tv_AscribedC
                                        (e, uu___, uu___1) ->
                                        (fun s ->
                                           FStar_Tactics_Result.Success
                                             (e, s))
                                    | uu___ ->
                                        (fun s ->
                                           FStar_Tactics_Result.Success
                                             (t1, s))))
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (177))
                                                (Prims.of_int (4))
                                                (Prims.of_int (180))
                                                (Prims.of_int (12)))))))
                         | FStar_Tactics_Result.Failed (e, ps'1) ->
                             FStar_Tactics_Result.Failed (e, ps'1)) t)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.Base.fst"
                               (Prims.of_int (176)) (Prims.of_int (2))
                               (Prims.of_int (180)) (Prims.of_int (15)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (prettify_term :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  = fun dbg -> fun t -> filter_ascriptions dbg t
type 'a bind_map = (FStar_Reflection_Types.bv * 'a) Prims.list
let bind_map_push :
  'a .
    'a bind_map ->
      FStar_Reflection_Types.bv ->
        'a -> (FStar_Reflection_Types.bv * 'a) Prims.list
  = fun m -> fun b -> fun x -> (b, x) :: m
let rec bind_map_get :
  'a .
    'a bind_map ->
      FStar_Reflection_Types.bv -> 'a FStar_Pervasives_Native.option
  =
  fun m ->
    fun b ->
      match m with
      | [] -> FStar_Pervasives_Native.None
      | (b', x)::m' ->
          if (FStar_Reflection_Builtins.compare_bv b b') = FStar_Order.Eq
          then FStar_Pervasives_Native.Some x
          else bind_map_get m' b
let rec bind_map_get_from_name :
  'a .
    'a bind_map ->
      Prims.string ->
        (FStar_Reflection_Types.bv * 'a) FStar_Pervasives_Native.option
  =
  fun m ->
    fun name ->
      match m with
      | [] -> FStar_Pervasives_Native.None
      | (b', x)::m' ->
          let b'v = FStar_Reflection_Builtins.inspect_bv b' in
          if b'v.FStar_Reflection_Data.bv_ppname = name
          then FStar_Pervasives_Native.Some (b', x)
          else bind_map_get_from_name m' name
type genv =
  {
  env: FStar_Reflection_Types.env ;
  bmap: (Prims.bool * FStar_Reflection_Types.term) bind_map ;
  svars: FStar_Reflection_Types.bv Prims.list }
let (__proj__Mkgenv__item__env : genv -> FStar_Reflection_Types.env) =
  fun projectee -> match projectee with | { env; bmap; svars;_} -> env
let (__proj__Mkgenv__item__bmap :
  genv -> (Prims.bool * FStar_Reflection_Types.term) bind_map) =
  fun projectee -> match projectee with | { env; bmap; svars;_} -> bmap
let (__proj__Mkgenv__item__svars :
  genv -> FStar_Reflection_Types.bv Prims.list) =
  fun projectee -> match projectee with | { env; bmap; svars;_} -> svars
let (get_env : genv -> FStar_Reflection_Types.env) = fun e -> e.env
let (get_bind_map :
  genv -> (Prims.bool * FStar_Reflection_Types.term) bind_map) =
  fun e -> e.bmap
let (mk_genv :
  FStar_Reflection_Types.env ->
    (Prims.bool * FStar_Reflection_Types.term) bind_map ->
      FStar_Reflection_Types.bv Prims.list -> genv)
  = fun env -> fun bmap -> fun svars -> { env; bmap; svars }
let (mk_init_genv : FStar_Reflection_Types.env -> genv) =
  fun env -> mk_genv env [] []
let (genv_to_string : genv -> Prims.string) =
  fun ge ->
    let binder_to_string b =
      Prims.strcat (abv_to_string (FStar_Reflection_Derived.bv_of_binder b))
        "\n" in
    let binders_str =
      FStar_List_Tot_Base.map binder_to_string
        (FStar_Reflection_Builtins.binders_of_env ge.env) in
    let bmap_elem_to_string e =
      let uu___ = e in
      match uu___ with
      | (bv, (abs, t)) ->
          Prims.strcat "("
            (Prims.strcat (abv_to_string bv)
               (Prims.strcat " -> ("
                  (Prims.strcat (Prims.string_of_bool abs)
                     (Prims.strcat ", "
                        (Prims.strcat
                           (FStar_Reflection_Builtins.term_to_string t)
                           "))\n"))))) in
    let bmap_str = FStar_List_Tot_Base.map bmap_elem_to_string ge.bmap in
    let svars_str =
      FStar_List_Tot_Base.map
        (fun bv -> Prims.strcat (abv_to_string bv) "\n") ge.svars in
    let flatten =
      FStar_List_Tot_Base.fold_left (fun x -> fun y -> Prims.strcat x y) "" in
    Prims.strcat "> env:\n"
      (Prims.strcat (flatten binders_str)
         (Prims.strcat "> bmap:\n"
            (Prims.strcat (flatten bmap_str)
               (Prims.strcat "> svars:\n" (flatten svars_str)))))
let (genv_get :
  genv ->
    FStar_Reflection_Types.bv ->
      (Prims.bool * FStar_Reflection_Types.term)
        FStar_Pervasives_Native.option)
  = fun ge -> fun b -> bind_map_get ge.bmap b
let (genv_get_from_name :
  genv ->
    Prims.string ->
      (FStar_Reflection_Types.bv * (Prims.bool *
        FStar_Reflection_Types.term)) FStar_Pervasives_Native.option)
  = fun ge -> fun name -> bind_map_get_from_name ge.bmap name
let (genv_push_bv :
  genv ->
    FStar_Reflection_Types.bv ->
      Prims.bool ->
        FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
          FStar_Tactics_Types.proofstate ->
            genv FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun b ->
      fun abs ->
        fun t ->
          fun ps ->
            match FStar_Tactics_Types.tracepoint
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (272)) (Prims.of_int (11))
                                   (Prims.of_int (272)) (Prims.of_int (22))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.Base.fst"
                             (Prims.of_int (273)) (Prims.of_int (2))
                             (Prims.of_int (278)) (Prims.of_int (25)))))
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
                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (272))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (272))
                                                    (Prims.of_int (22))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (273))
                                              (Prims.of_int (2))
                                              (Prims.of_int (278))
                                              (Prims.of_int (25))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (273))
                                        (Prims.of_int (11))
                                        (Prims.of_int (273))
                                        (Prims.of_int (47))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (274)) (Prims.of_int (2))
                                  (Prims.of_int (278)) (Prims.of_int (25)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (22))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (273))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (278))
                                                               (Prims.of_int (25))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (273))
                                                         (Prims.of_int (47))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (274))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (278))
                                                   (Prims.of_int (25))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (274))
                                             (Prims.of_int (15))
                                             (Prims.of_int (274))
                                             (Prims.of_int (74))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                       (Prims.of_int (275))
                                       (Prims.of_int (2))
                                       (Prims.of_int (278))
                                       (Prims.of_int (25)))))
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
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (25))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (47))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (25))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                                              (Prims.of_int (274))
                                                              (Prims.of_int (15))
                                                              (Prims.of_int (274))
                                                              (Prims.of_int (74))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (275))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (278))
                                                        (Prims.of_int (25))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (275))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (275))
                                                  (Prims.of_int (32))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (276))
                                            (Prims.of_int (2))
                                            (Prims.of_int (278))
                                            (Prims.of_int (25)))))
                           with
                           | true ->
                               (match (if
                                         FStar_Pervasives_Native.uu___is_Some
                                           t
                                       then
                                         fun s ->
                                           FStar_Tactics_Result.Success
                                             ((FStar_Pervasives_Native.__proj__Some__item__v
                                                 t), s)
                                       else
                                         FStar_Tactics_Builtins.pack
                                           (FStar_Reflection_Data.Tv_Var b))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (47))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (74))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (25))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (275))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (275))
                                                                (Prims.of_int (32))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (276))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (278))
                                                          (Prims.of_int (25))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (276))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (276))
                                                    (Prims.of_int (57))))))
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (278))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (278))
                                                      (Prims.of_int (25)))))
                                     with
                                     | true ->
                                         FStar_Tactics_Result.Success
                                           ((mk_genv
                                               (FStar_Reflection_Builtins.push_binder
                                                  ge.env
                                                  (FStar_Reflection_Derived.mk_binder
                                                     b))
                                               (bind_map_push ge.bmap b
                                                  (abs, a))
                                               (if
                                                  FStar_Pervasives_Native.uu___is_Some
                                                    (genv_get_from_name ge
                                                       (FStar_Reflection_Derived.name_of_bv
                                                          b))
                                                then
                                                  (FStar_Pervasives_Native.fst
                                                     (FStar_Pervasives_Native.__proj__Some__item__v
                                                        (genv_get_from_name
                                                           ge
                                                           (FStar_Reflection_Derived.name_of_bv
                                                              b))))
                                                  :: (ge.svars)
                                                else ge.svars)),
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                                         (Prims.of_int (278))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (278))
                                                         (Prims.of_int (25))))))))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')))))
let (genv_push_binder :
  genv ->
    FStar_Reflection_Types.binder ->
      Prims.bool ->
        FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
          FStar_Tactics_Types.proofstate ->
            genv FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun b ->
      fun abs ->
        fun t ->
          genv_push_bv ge (FStar_Reflection_Derived.bv_of_binder b) abs t
let (bv_is_shadowed : genv -> FStar_Reflection_Types.bv -> Prims.bool) =
  fun ge -> fun bv -> FStar_List_Tot_Base.existsb (bv_eq bv) ge.svars
let (binder_is_shadowed :
  genv -> FStar_Reflection_Types.binder -> Prims.bool) =
  fun ge ->
    fun b -> bv_is_shadowed ge (FStar_Reflection_Derived.bv_of_binder b)
let (find_shadowed_bvs :
  genv ->
    FStar_Reflection_Types.bv Prims.list ->
      (FStar_Reflection_Types.bv * Prims.bool) Prims.list)
  =
  fun ge ->
    fun bl ->
      FStar_List_Tot_Base.map (fun b -> (b, (bv_is_shadowed ge b))) bl
let (find_shadowed_binders :
  genv ->
    FStar_Reflection_Types.binder Prims.list ->
      (FStar_Reflection_Types.binder * Prims.bool) Prims.list)
  =
  fun ge ->
    fun bl ->
      FStar_List_Tot_Base.map (fun b -> (b, (binder_is_shadowed ge b))) bl
let (bv_is_abstract : genv -> FStar_Reflection_Types.bv -> Prims.bool) =
  fun ge ->
    fun bv ->
      match genv_get ge bv with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (abs, uu___) -> abs
let (binder_is_abstract :
  genv -> FStar_Reflection_Types.binder -> Prims.bool) =
  fun ge ->
    fun b -> bv_is_abstract ge (FStar_Reflection_Derived.bv_of_binder b)
let (genv_abstract_bvs : genv -> FStar_Reflection_Types.bv Prims.list) =
  fun ge ->
    let abs =
      FStar_List_Tot_Base.filter
        (fun uu___ -> match uu___ with | (uu___1, (abs1, uu___2)) -> abs1)
        ge.bmap in
    FStar_List_Tot_Base.map
      (fun uu___ -> match uu___ with | (bv, uu___1) -> bv) abs
let rec (_fresh_bv :
  Prims.string Prims.list ->
    Prims.string ->
      Prims.int ->
        FStar_Reflection_Types.typ ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.bv FStar_Tactics_Result.__result)
  =
  fun binder_names ->
    fun basename ->
      fun i ->
        fun ty ->
          fun ps ->
            match FStar_Tactics_Types.tracepoint
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (315)) (Prims.of_int (13))
                                   (Prims.of_int (315)) (Prims.of_int (39))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.Base.fst"
                             (Prims.of_int (318)) (Prims.of_int (2))
                             (Prims.of_int (319)) (Prims.of_int (29)))))
            with
            | true ->
                (if
                   FStar_List_Tot_Base.mem
                     (Prims.strcat basename (Prims.string_of_int i))
                     binder_names
                 then _fresh_bv binder_names basename (i + Prims.int_one) ty
                 else
                   FStar_Tactics_Builtins.fresh_bv_named
                     (Prims.strcat basename (Prims.string_of_int i)) ty)
                  (FStar_Tactics_Types.decr_depth
                     (FStar_Tactics_Types.set_proofstate_range
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (315)) (Prims.of_int (13))
                                    (Prims.of_int (315)) (Prims.of_int (39))))))
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (318)) (Prims.of_int (2))
                              (Prims.of_int (319)) (Prims.of_int (29))))))
let (fresh_bv :
  FStar_Reflection_Types.env ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.bv FStar_Tactics_Result.__result)
  =
  fun e ->
    fun basename ->
      fun ty ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (322)) (Prims.of_int (16))
                                 (Prims.of_int (322)) (Prims.of_int (32))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (323)) (Prims.of_int (2))
                           (Prims.of_int (324)) (Prims.of_int (38)))))
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
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (322))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (322))
                                                  (Prims.of_int (32))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (323))
                                            (Prims.of_int (2))
                                            (Prims.of_int (324))
                                            (Prims.of_int (38))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (323))
                                      (Prims.of_int (21))
                                      (Prims.of_int (323))
                                      (Prims.of_int (56))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (324)) (Prims.of_int (2))
                                (Prims.of_int (324)) (Prims.of_int (38)))))
               with
               | true ->
                   (_fresh_bv
                      (FStar_List_Tot_Base.map
                         FStar_Reflection_Derived.name_of_binder
                         (FStar_Reflection_Builtins.binders_of_env e))
                      basename Prims.int_zero ty)
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
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (322))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (322))
                                                   (Prims.of_int (32))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (323))
                                             (Prims.of_int (2))
                                             (Prims.of_int (324))
                                             (Prims.of_int (38))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                       (Prims.of_int (323))
                                       (Prims.of_int (21))
                                       (Prims.of_int (323))
                                       (Prims.of_int (56))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (324)) (Prims.of_int (2))
                                 (Prims.of_int (324)) (Prims.of_int (38)))))))
let (fresh_binder :
  FStar_Reflection_Types.env ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun e ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (fresh_bv e basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (327)) (Prims.of_int (11))
                              (Prims.of_int (327)) (Prims.of_int (33))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (328)) (Prims.of_int (2))
                                (Prims.of_int (328)) (Prims.of_int (14)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     ((FStar_Reflection_Derived.mk_binder a),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (328)) (Prims.of_int (2))
                                   (Prims.of_int (328)) (Prims.of_int (14))))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (genv_push_fresh_binder :
  genv ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (genv * FStar_Reflection_Types.binder)
            FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (fresh_binder ge.env basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (331)) (Prims.of_int (10))
                              (Prims.of_int (331)) (Prims.of_int (41))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (333)) (Prims.of_int (2))
                                (Prims.of_int (334)) (Prims.of_int (8)))))
               with
               | true ->
                   (match (genv_push_binder ge a true
                             FStar_Pervasives_Native.None)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (333))
                                              (Prims.of_int (2))
                                              (Prims.of_int (334))
                                              (Prims.of_int (8))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (333))
                                        (Prims.of_int (12))
                                        (Prims.of_int (333))
                                        (Prims.of_int (43))))))
                    with
                    | FStar_Tactics_Result.Success (a1, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                          (Prims.of_int (334))
                                          (Prims.of_int (2))
                                          (Prims.of_int (334))
                                          (Prims.of_int (8)))))
                         with
                         | true ->
                             FStar_Tactics_Result.Success
                               ((a1, a),
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (334))
                                             (Prims.of_int (2))
                                             (Prims.of_int (334))
                                             (Prims.of_int (8))))))))
                    | FStar_Tactics_Result.Failed (e, ps'1) ->
                        FStar_Tactics_Result.Failed (e, ps'1)))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (push_fresh_binder :
  FStar_Reflection_Types.env ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.env * FStar_Reflection_Types.binder)
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (fresh_binder e basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (338)) (Prims.of_int (10))
                              (Prims.of_int (338)) (Prims.of_int (36))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (339)) (Prims.of_int (2))
                                (Prims.of_int (340)) (Prims.of_int (7)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     (((FStar_Reflection_Builtins.push_binder e a), a),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (339)) (Prims.of_int (2))
                                   (Prims.of_int (340)) (Prims.of_int (7))))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (genv_push_fresh_bv :
  genv ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (genv * FStar_Reflection_Types.bv) FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (genv_push_fresh_binder ge basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (343)) (Prims.of_int (15))
                              (Prims.of_int (343)) (Prims.of_int (52))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (343)) (Prims.of_int (2))
                                (Prims.of_int (344)) (Prims.of_int (21)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     (((match a with
                        | (ge', b) ->
                            (ge', (FStar_Reflection_Derived.bv_of_binder b)))),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (343)) (Prims.of_int (2))
                                   (Prims.of_int (344)) (Prims.of_int (21))))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (push_fresh_var :
  FStar_Reflection_Types.env ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            FStar_Reflection_Types.env) FStar_Tactics_Result.__result)
  =
  fun e0 ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (push_fresh_binder e0 basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (348)) (Prims.of_int (15))
                              (Prims.of_int (348)) (Prims.of_int (47))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (348)) (Prims.of_int (2))
                                (Prims.of_int (350)) (Prims.of_int (12)))))
               with
               | true ->
                   ((match a with
                     | (e1, b1) ->
                         (fun ps1 ->
                            match (FStar_Tactics_Builtins.pack
                                     (FStar_Reflection_Data.Tv_Var
                                        (FStar_Reflection_Derived.bv_of_binder
                                           b1)))
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (349))
                                                (Prims.of_int (11))
                                                (Prims.of_int (349))
                                                (Prims.of_int (42))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (350))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (350))
                                                  (Prims.of_int (12)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       ((a1, b1, e1),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                                     (Prims.of_int (350))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (350))
                                                     (Prims.of_int (12))))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (348)) (Prims.of_int (2))
                                 (Prims.of_int (350)) (Prims.of_int (12)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (genv_push_fresh_var :
  genv ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            genv) FStar_Tactics_Result.__result)
  =
  fun ge0 ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (genv_push_fresh_binder ge0 basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (354)) (Prims.of_int (16))
                              (Prims.of_int (354)) (Prims.of_int (54))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (354)) (Prims.of_int (2))
                                (Prims.of_int (356)) (Prims.of_int (13)))))
               with
               | true ->
                   ((match a with
                     | (ge1, b1) ->
                         (fun ps1 ->
                            match (FStar_Tactics_Builtins.pack
                                     (FStar_Reflection_Data.Tv_Var
                                        (FStar_Reflection_Derived.bv_of_binder
                                           b1)))
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (355))
                                                (Prims.of_int (11))
                                                (Prims.of_int (355))
                                                (Prims.of_int (42))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (356))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (356))
                                                  (Prims.of_int (13)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       ((a1, b1, ge1),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                                     (Prims.of_int (356))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (356))
                                                     (Prims.of_int (13))))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (354)) (Prims.of_int (2))
                                 (Prims.of_int (356)) (Prims.of_int (13)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (push_two_fresh_vars :
  FStar_Reflection_Types.env ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            FStar_Reflection_Types.env) FStar_Tactics_Result.__result)
  =
  fun e0 ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (push_fresh_binder e0 basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (360)) (Prims.of_int (15))
                              (Prims.of_int (360)) (Prims.of_int (47))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (360)) (Prims.of_int (2))
                                (Prims.of_int (364)) (Prims.of_int (20)))))
               with
               | true ->
                   ((match a with
                     | (e1, b1) ->
                         (fun ps1 ->
                            match (push_fresh_binder e1 basename ty)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (361))
                                                (Prims.of_int (15))
                                                (Prims.of_int (361))
                                                (Prims.of_int (47))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (361))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (364))
                                                  (Prims.of_int (20)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (e2, b2) ->
                                           (fun ps2 ->
                                              match (FStar_Tactics_Builtins.pack
                                                       (FStar_Reflection_Data.Tv_Var
                                                          (FStar_Reflection_Derived.bv_of_binder
                                                             b1)))
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (362))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (362))
                                                                  (Prims.of_int (42))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (20)))))
                                                   with
                                                   | true ->
                                                       (match (FStar_Tactics_Builtins.pack
                                                                 (FStar_Reflection_Data.Tv_Var
                                                                    (
                                                                    FStar_Reflection_Derived.bv_of_binder
                                                                    b2)))
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (42))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a3, ps'3) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (20)))))
                                                             with
                                                             | true ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((a2, b1,
                                                                    a3, b2,
                                                                    e2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (20))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'3) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'3)))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'2))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (361))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (20)))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (360)) (Prims.of_int (2))
                                 (Prims.of_int (364)) (Prims.of_int (20)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (genv_push_two_fresh_vars :
  genv ->
    Prims.string ->
      FStar_Reflection_Types.typ ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            FStar_Reflection_Types.term * FStar_Reflection_Types.binder *
            genv) FStar_Tactics_Result.__result)
  =
  fun ge0 ->
    fun basename ->
      fun ty ->
        fun ps ->
          match (genv_push_fresh_binder ge0 basename ty)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (368)) (Prims.of_int (16))
                              (Prims.of_int (368)) (Prims.of_int (54))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (368)) (Prims.of_int (2))
                                (Prims.of_int (372)) (Prims.of_int (21)))))
               with
               | true ->
                   ((match a with
                     | (ge1, b1) ->
                         (fun ps1 ->
                            match (genv_push_fresh_binder ge1 basename ty)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (369))
                                                (Prims.of_int (16))
                                                (Prims.of_int (369))
                                                (Prims.of_int (54))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (369))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (372))
                                                  (Prims.of_int (21)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (ge2, b2) ->
                                           (fun ps2 ->
                                              match (FStar_Tactics_Builtins.pack
                                                       (FStar_Reflection_Data.Tv_Var
                                                          (FStar_Reflection_Derived.bv_of_binder
                                                             b1)))
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (370))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (370))
                                                                  (Prims.of_int (42))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (21)))))
                                                   with
                                                   | true ->
                                                       (match (FStar_Tactics_Builtins.pack
                                                                 (FStar_Reflection_Data.Tv_Var
                                                                    (
                                                                    FStar_Reflection_Derived.bv_of_binder
                                                                    b2)))
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (42))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a3, ps'3) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (21)))))
                                                             with
                                                             | true ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((a2, b1,
                                                                    a3, b2,
                                                                    ge2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (21))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'3) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'3)))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'2))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (369))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (372))
                                                   (Prims.of_int (21)))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (368)) (Prims.of_int (2))
                                 (Prims.of_int (372)) (Prims.of_int (21)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (norm_apply_subst :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      fun subst ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (386)) (Prims.of_int (15))
                                 (Prims.of_int (386)) (Prims.of_int (26))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (386)) (Prims.of_int (2))
                           (Prims.of_int (390)) (Prims.of_int (23)))))
          with
          | true ->
              ((match unzip subst with
                | (bl, vl) ->
                    (fun ps1 ->
                       match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (387))
                                              (Prims.of_int (11))
                                              (Prims.of_int (387))
                                              (Prims.of_int (36))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (388))
                                        (Prims.of_int (2))
                                        (Prims.of_int (390))
                                        (Prims.of_int (23)))))
                       with
                       | true ->
                           (match (FStar_Tactics_Derived.mk_abs
                                     (FStar_List_Tot_Base.map
                                        FStar_Reflection_Derived.mk_binder bl)
                                     t)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (387))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (387))
                                                            (Prims.of_int (36))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (388))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (390))
                                                      (Prims.of_int (23))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (388))
                                                (Prims.of_int (11))
                                                (Prims.of_int (388))
                                                (Prims.of_int (22))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (389))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (390))
                                                  (Prims.of_int (23)))))
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
                                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (389))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (390))
                                                                   (Prims.of_int (23))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (11))
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (25))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                                       (Prims.of_int (390))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (390))
                                                       (Prims.of_int (23)))))
                                      with
                                      | true ->
                                          (FStar_Tactics_Builtins.norm_term_env
                                             e []
                                             (FStar_Reflection_Derived.mk_e_app
                                                a vl))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (23))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                                              (Prims.of_int (389))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (389))
                                                              (Prims.of_int (25))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (390))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (390))
                                                        (Prims.of_int (23))))))))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps')))))
                (FStar_Tactics_Types.decr_depth
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (386)) (Prims.of_int (15))
                                  (Prims.of_int (386)) (Prims.of_int (26))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (386)) (Prims.of_int (2))
                            (Prims.of_int (390)) (Prims.of_int (23))))))
let (norm_apply_subst_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun c ->
      fun subst ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (393)) (Prims.of_int (14))
                                 (Prims.of_int (393)) (Prims.of_int (51))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (394)) (Prims.of_int (2))
                           (Prims.of_int (417)) (Prims.of_int (49)))))
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
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (393))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (393))
                                                  (Prims.of_int (51))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (394))
                                            (Prims.of_int (2))
                                            (Prims.of_int (417))
                                            (Prims.of_int (49))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (395)) (Prims.of_int (4))
                                      (Prims.of_int (398))
                                      (Prims.of_int (34))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (400)) (Prims.of_int (2))
                                (Prims.of_int (417)) (Prims.of_int (49)))))
               with
               | true ->
                   ((match FStar_Reflection_Builtins.inspect_comp c with
                     | FStar_Reflection_Data.C_Total (ret, decr) ->
                         (fun ps1 ->
                            match (norm_apply_subst e ret subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (402))
                                                (Prims.of_int (14))
                                                (Prims.of_int (402))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (403))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (404))
                                                  (Prims.of_int (32)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun x ->
                                                  norm_apply_subst e x subst)
                                               decr)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (403))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (404))
                                                                (Prims.of_int (32))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (403))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (403))
                                                          (Prims.of_int (29))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (404))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (404))
                                                            (Prims.of_int (32)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_Total
                                                        (a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (404))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (404))
                                                               (Prims.of_int (32))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_GTotal (ret, decr) ->
                         (fun ps1 ->
                            match (norm_apply_subst e ret subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (406))
                                                (Prims.of_int (14))
                                                (Prims.of_int (406))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (407))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (408))
                                                  (Prims.of_int (33)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun x ->
                                                  norm_apply_subst e x subst)
                                               decr)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (407))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (408))
                                                                (Prims.of_int (33))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (29))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (408))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (408))
                                                            (Prims.of_int (33)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_GTotal
                                                        (a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (408))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (408))
                                                               (Prims.of_int (33))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_Lemma (pre, post, patterns) ->
                         (fun ps1 ->
                            match (norm_apply_subst e pre subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (410))
                                                (Prims.of_int (14))
                                                (Prims.of_int (410))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (411))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (413))
                                                  (Prims.of_int (41)))))
                                 with
                                 | true ->
                                     (match (norm_apply_subst e post subst)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (411))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (413))
                                                                (Prims.of_int (41))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (411))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (411))
                                                          (Prims.of_int (25))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (412))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (413))
                                                            (Prims.of_int (41)))))
                                           with
                                           | true ->
                                               (match (norm_apply_subst e
                                                         patterns subst)
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (41))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (33))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a2, ps'2) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (41)))))
                                                     with
                                                     | true ->
                                                         FStar_Tactics_Result.Success
                                                           ((FStar_Reflection_Builtins.pack_comp
                                                               (FStar_Reflection_Data.C_Lemma
                                                                  (a, a1, a2))),
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (41))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e1, ps'2) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e1, ps'2)))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_Eff
                         (us, eff_name, result, eff_args) ->
                         (fun ps1 ->
                            match (norm_apply_subst e result subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (415))
                                                (Prims.of_int (17))
                                                (Prims.of_int (415))
                                                (Prims.of_int (29))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (416))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (417))
                                                  (Prims.of_int (49)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun uu___ ->
                                                  match uu___ with
                                                  | (x, a1) ->
                                                      (fun ps2 ->
                                                         match (norm_apply_subst
                                                                  e x subst)
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (46))))))
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a2, ps'1) ->
                                                             (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (66)))))
                                                              with
                                                              | true ->
                                                                  (match 
                                                                    (match a1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Implicit
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a1, s))
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Explicit
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a1, s))
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Meta
                                                                    t ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (norm_apply_subst
                                                                    e t subst)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (34))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Data.Q_Meta
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (34))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (65))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (66)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2, a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (66))))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)))
                                                         | FStar_Tactics_Result.Failed
                                                             (e1, ps'1) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e1, ps'1)))
                                               eff_args)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (416))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (49))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (416))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (416))
                                                          (Prims.of_int (76))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (417))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (417))
                                                            (Prims.of_int (49)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_Eff
                                                        (us, eff_name, a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (417))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (417))
                                                               (Prims.of_int (49))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))))
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
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (393))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (393))
                                                   (Prims.of_int (51))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (394))
                                             (Prims.of_int (2))
                                             (Prims.of_int (417))
                                             (Prims.of_int (49))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                       (Prims.of_int (395))
                                       (Prims.of_int (4))
                                       (Prims.of_int (398))
                                       (Prims.of_int (34))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (400)) (Prims.of_int (2))
                                 (Prims.of_int (417)) (Prims.of_int (49)))))))
let rec (deep_apply_subst :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      fun subst ->
        fun ps ->
          match (FStar_Tactics_Builtins.inspect t)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (436)) (Prims.of_int (8))
                              (Prims.of_int (436)) (Prims.of_int (17))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (436)) (Prims.of_int (2))
                                (Prims.of_int (504)) (Prims.of_int (5)))))
               with
               | true ->
                   ((match a with
                     | FStar_Reflection_Data.Tv_Var b ->
                         (fun s ->
                            FStar_Tactics_Result.Success
                              ((match bind_map_get subst b with
                                | FStar_Pervasives_Native.None -> t
                                | FStar_Pervasives_Native.Some t' -> t'), s))
                     | FStar_Reflection_Data.Tv_BVar b ->
                         (fun s ->
                            FStar_Tactics_Result.Success
                              ((match bind_map_get subst b with
                                | FStar_Pervasives_Native.None -> t
                                | FStar_Pervasives_Native.Some t' -> t'), s))
                     | FStar_Reflection_Data.Tv_FVar uu___ ->
                         (fun s -> FStar_Tactics_Result.Success (t, s))
                     | FStar_Reflection_Data.Tv_App (hd, (a1, qual)) ->
                         (fun ps1 ->
                            match (deep_apply_subst e hd subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (450))
                                                (Prims.of_int (13))
                                                (Prims.of_int (450))
                                                (Prims.of_int (40))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (451))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (452))
                                                  (Prims.of_int (30)))))
                                 with
                                 | true ->
                                     (match (deep_apply_subst e a1 subst)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (451))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (452))
                                                                (Prims.of_int (30))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (451))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (451))
                                                          (Prims.of_int (38))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (452))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (452))
                                                            (Prims.of_int (30)))))
                                           with
                                           | true ->
                                               (FStar_Tactics_Builtins.pack
                                                  (FStar_Reflection_Data.Tv_App
                                                     (a2, (a3, qual))))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (452))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (452))
                                                             (Prims.of_int (30)))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'2) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'2)))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_Abs (br, body) ->
                         (fun ps1 ->
                            match (deep_apply_subst e body subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (454))
                                                (Prims.of_int (15))
                                                (Prims.of_int (454))
                                                (Prims.of_int (44))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (455))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (455))
                                                  (Prims.of_int (25)))))
                                 with
                                 | true ->
                                     (FStar_Tactics_Builtins.pack
                                        (FStar_Reflection_Data.Tv_Abs
                                           (br, a1)))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (455))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (455))
                                                   (Prims.of_int (25)))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_Arrow (br, c) ->
                         (fun ps1 ->
                            match (deep_apply_subst_in_binder e br subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (457))
                                                (Prims.of_int (20))
                                                (Prims.of_int (457))
                                                (Prims.of_int (57))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (457))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (459))
                                                  (Prims.of_int (24)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (br1, subst1) ->
                                           (fun ps2 ->
                                              match (deep_apply_subst_in_comp
                                                       e c subst1)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (458))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (458))
                                                                  (Prims.of_int (46))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (24)))))
                                                   with
                                                   | true ->
                                                       (FStar_Tactics_Builtins.pack
                                                          (FStar_Reflection_Data.Tv_Arrow
                                                             (br1, a2)))
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (24)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e1, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e1, ps'2))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (457))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (459))
                                                   (Prims.of_int (24)))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_Type () ->
                         (fun s -> FStar_Tactics_Result.Success (t, s))
                     | FStar_Reflection_Data.Tv_Refine (bv, ref) ->
                         (fun ps1 ->
                            match (deep_apply_subst_in_bv e bv subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (462))
                                                (Prims.of_int (20))
                                                (Prims.of_int (462))
                                                (Prims.of_int (53))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (462))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (464))
                                                  (Prims.of_int (27)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (bv1, subst1) ->
                                           (fun ps2 ->
                                              match (deep_apply_subst e ref
                                                       subst1)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (463))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (463))
                                                                  (Prims.of_int (42))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (27)))))
                                                   with
                                                   | true ->
                                                       (FStar_Tactics_Builtins.pack
                                                          (FStar_Reflection_Data.Tv_Refine
                                                             (bv1, a2)))
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (27)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e1, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e1, ps'2))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (462))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (464))
                                                   (Prims.of_int (27)))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_Const uu___ ->
                         (fun s -> FStar_Tactics_Result.Success (t, s))
                     | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
                         (fun s -> FStar_Tactics_Result.Success (t, s))
                     | FStar_Reflection_Data.Tv_Let
                         (recf, attrs, bv, def, body) ->
                         (fun ps1 ->
                            match (deep_apply_subst_in_bv e bv subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (469))
                                                (Prims.of_int (20))
                                                (Prims.of_int (469))
                                                (Prims.of_int (53))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (469))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (472))
                                                  (Prims.of_int (37)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (bv1, subst1) ->
                                           (fun ps2 ->
                                              match (deep_apply_subst e def
                                                       subst1)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (470))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (470))
                                                                  (Prims.of_int (42))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (37)))))
                                                   with
                                                   | true ->
                                                       (match (deep_apply_subst
                                                                 e body
                                                                 subst1)
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (37))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (44))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a3, ps'3) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (37)))))
                                                             with
                                                             | true ->
                                                                 (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_Let
                                                                    (recf,
                                                                    [], bv1,
                                                                    a2, a3)))
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (37)))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e1, ps'3) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e1, ps'3)))
                                              | FStar_Tactics_Result.Failed
                                                  (e1, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e1, ps'2))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (469))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (472))
                                                   (Prims.of_int (37)))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_Match
                         (scrutinee, ret_opt, branches) ->
                         (fun ps1 ->
                            match (deep_apply_subst e scrutinee subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (474))
                                                (Prims.of_int (20))
                                                (Prims.of_int (474))
                                                (Prims.of_int (54))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (475))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (491))
                                                  (Prims.of_int (46)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map_opt
                                               (fun ret ->
                                                  match ret with
                                                  | (FStar_Pervasives.Inl t1,
                                                     tacopt) ->
                                                      (fun ps2 ->
                                                         match match 
                                                                 (deep_apply_subst
                                                                    e t1
                                                                    subst)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (40))))))
                                                               with
                                                               | FStar_Tactics_Result.Success
                                                                   (a2, ps'2)
                                                                   ->
                                                                   (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (40)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives.Inl
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (40))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e1, ps'2)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a2, ps'2) ->
                                                             (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (64)))))
                                                              with
                                                              | true ->
                                                                  (match 
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (fun tac
                                                                    ->
                                                                    deep_apply_subst
                                                                    e tac
                                                                    subst)
                                                                    tacopt)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (64))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (64))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (64)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2, a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (64))))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                         | FStar_Tactics_Result.Failed
                                                             (e1, ps'2) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e1, ps'2))
                                                  | (FStar_Pervasives.Inr c,
                                                     tacopt) ->
                                                      (fun ps2 ->
                                                         match match 
                                                                 (deep_apply_subst_in_comp
                                                                    e c subst)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (48))))))
                                                               with
                                                               | FStar_Tactics_Result.Success
                                                                   (a2, ps'2)
                                                                   ->
                                                                   (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (48)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives.Inr
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (48))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e1, ps'2)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a2, ps'2) ->
                                                             (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (64)))))
                                                              with
                                                              | true ->
                                                                  (match 
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (fun tac
                                                                    ->
                                                                    deep_apply_subst
                                                                    e tac
                                                                    subst)
                                                                    tacopt)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (64))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (64))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (64)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2, a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (64))))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                         | FStar_Tactics_Result.Failed
                                                             (e1, ps'2) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e1, ps'2)))
                                               ret_opt)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (475))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (491))
                                                                (Prims.of_int (46))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (475))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (482))
                                                          (Prims.of_int (73))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (484))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (491))
                                                            (Prims.of_int (46)))))
                                           with
                                           | true ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (13))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                 (Prims.of_int (490))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (491))
                                                                 (Prims.of_int (46)))))
                                                with
                                                | true ->
                                                    (match (FStar_Tactics_Util.map
                                                              (fun branch ->
                                                                 fun ps2 ->
                                                                   match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (17)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    ((match branch
                                                                    with
                                                                    | (pat,
                                                                    tm) ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (deep_apply_subst_in_pattern
                                                                    e pat
                                                                    subst)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (62))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | (pat1,
                                                                    subst1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (deep_apply_subst
                                                                    e tm
                                                                    subst1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (42))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (13)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((pat1,
                                                                    a4),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (13))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (20)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (17)))))))
                                                              branches)
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (58))))))
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a3, ps'3) ->
                                                         (match FStar_Tactics_Types.tracepoint
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46)))))
                                                          with
                                                          | true ->
                                                              (FStar_Tactics_Builtins.pack
                                                                 (FStar_Reflection_Data.Tv_Match
                                                                    (a1, a2,
                                                                    a3)))
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (46)))))))
                                                     | FStar_Tactics_Result.Failed
                                                         (e1, ps'3) ->
                                                         FStar_Tactics_Result.Failed
                                                           (e1, ps'3))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'2) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'2)))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_AscribedT (exp, ty, tac) ->
                         (fun ps1 ->
                            match (deep_apply_subst e exp subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (493))
                                                (Prims.of_int (14))
                                                (Prims.of_int (493))
                                                (Prims.of_int (42))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (494))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (496))
                                                  (Prims.of_int (35)))))
                                 with
                                 | true ->
                                     (match (deep_apply_subst e ty subst)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (494))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (496))
                                                                (Prims.of_int (35))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (494))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (494))
                                                          (Prims.of_int (40))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (496))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (496))
                                                            (Prims.of_int (35)))))
                                           with
                                           | true ->
                                               (FStar_Tactics_Builtins.pack
                                                  (FStar_Reflection_Data.Tv_AscribedT
                                                     (a1, a2,
                                                       FStar_Pervasives_Native.None)))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (496))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (496))
                                                             (Prims.of_int (35)))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'2) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'2)))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Reflection_Data.Tv_AscribedC (exp, c, tac) ->
                         (fun ps1 ->
                            match (deep_apply_subst e exp subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (498))
                                                (Prims.of_int (14))
                                                (Prims.of_int (498))
                                                (Prims.of_int (42))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (499))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (501))
                                                  (Prims.of_int (34)))))
                                 with
                                 | true ->
                                     (match (deep_apply_subst_in_comp e c
                                               subst)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (499))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (501))
                                                                (Prims.of_int (34))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (499))
                                                          (Prims.of_int (46))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (501))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (501))
                                                            (Prims.of_int (34)))))
                                           with
                                           | true ->
                                               (FStar_Tactics_Builtins.pack
                                                  (FStar_Reflection_Data.Tv_AscribedC
                                                     (a1, a2,
                                                       FStar_Pervasives_Native.None)))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (501))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (501))
                                                             (Prims.of_int (34)))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'2) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'2)))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | uu___ ->
                         (fun s -> FStar_Tactics_Result.Success (t, s))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (436)) (Prims.of_int (2))
                                 (Prims.of_int (504)) (Prims.of_int (5)))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
and (deep_apply_subst_in_bv :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.bv ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.bv * (FStar_Reflection_Types.bv *
            FStar_Reflection_Types.term) Prims.list)
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun bv ->
      fun subst ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (507)) (Prims.of_int (12))
                                 (Prims.of_int (507)) (Prims.of_int (25))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (508)) (Prims.of_int (2))
                           (Prims.of_int (510)) (Prims.of_int (37)))))
          with
          | true ->
              (match (deep_apply_subst e
                        (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_sort
                        subst)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (507))
                                               (Prims.of_int (12))
                                               (Prims.of_int (507))
                                               (Prims.of_int (25))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                         (Prims.of_int (508))
                                         (Prims.of_int (2))
                                         (Prims.of_int (510))
                                         (Prims.of_int (37))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (508)) (Prims.of_int (11))
                                   (Prims.of_int (508)) (Prims.of_int (47))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (509)) (Prims.of_int (2))
                                     (Prims.of_int (510)) (Prims.of_int (37)))))
                    with
                    | true ->
                        (match (FStar_Tactics_Builtins.fresh_bv_named
                                  (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_ppname
                                  a)
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (509))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (510))
                                                   (Prims.of_int (37))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (509))
                                             (Prims.of_int (12))
                                             (Prims.of_int (509))
                                             (Prims.of_int (51))))))
                         with
                         | FStar_Tactics_Result.Success (a1, ps'1) ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (510))
                                               (Prims.of_int (2))
                                               (Prims.of_int (510))
                                               (Prims.of_int (37)))))
                              with
                              | true ->
                                  (match match match (FStar_Tactics_Builtins.pack
                                                        (FStar_Reflection_Data.Tv_Var
                                                           a1))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (37))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (32))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (30))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (510))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (510))
                                                                   (Prims.of_int (29))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a2, ps'2) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (30)))))
                                                    with
                                                    | true ->
                                                        FStar_Tactics_Result.Success
                                                          ((bv, a2),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (30))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e1, ps'2) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e1, ps'2)
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a2, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (510))
                                                               (Prims.of_int (30))
                                                               (Prims.of_int (510))
                                                               (Prims.of_int (32)))))
                                              with
                                              | true ->
                                                  FStar_Tactics_Result.Success
                                                    ((a2 :: subst),
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                  (Prims.of_int (510))
                                                                  (Prims.of_int (30))
                                                                  (Prims.of_int (510))
                                                                  (Prims.of_int (32))))))))
                                         | FStar_Tactics_Result.Failed
                                             (e1, ps'2) ->
                                             FStar_Tactics_Result.Failed
                                               (e1, ps'2)
                                   with
                                   | FStar_Tactics_Result.Success (a2, ps'2)
                                       ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                                         (Prims.of_int (510))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (510))
                                                         (Prims.of_int (37)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((a1, a2),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (510))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (510))
                                                            (Prims.of_int (37))))))))
                                   | FStar_Tactics_Result.Failed (e1, ps'2)
                                       ->
                                       FStar_Tactics_Result.Failed (e1, ps'2)))
                         | FStar_Tactics_Result.Failed (e1, ps'1) ->
                             FStar_Tactics_Result.Failed (e1, ps'1)))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
and (deep_apply_subst_in_binder :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.binder ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Types.binder * (FStar_Reflection_Types.bv *
            FStar_Reflection_Types.term) Prims.list)
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun br ->
      fun subst ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (516)) (Prims.of_int (26))
                                 (Prims.of_int (516)) (Prims.of_int (43))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (516)) (Prims.of_int (2))
                           (Prims.of_int (518)) (Prims.of_int (34)))))
          with
          | true ->
              ((match FStar_Reflection_Builtins.inspect_binder br with
                | (bv, (qual, attrs)) ->
                    (fun ps1 ->
                       match (deep_apply_subst_in_bv e bv subst)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.Base.fst"
                                           (Prims.of_int (517))
                                           (Prims.of_int (18))
                                           (Prims.of_int (517))
                                           (Prims.of_int (51))))))
                       with
                       | FStar_Tactics_Result.Success (a, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (517))
                                             (Prims.of_int (2))
                                             (Prims.of_int (518))
                                             (Prims.of_int (34)))))
                            with
                            | true ->
                                FStar_Tactics_Result.Success
                                  (((match a with
                                     | (bv1, subst1) ->
                                         ((FStar_Reflection_Builtins.pack_binder
                                             bv1 qual attrs), subst1))),
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (517))
                                                (Prims.of_int (2))
                                                (Prims.of_int (518))
                                                (Prims.of_int (34))))))))
                       | FStar_Tactics_Result.Failed (e1, ps') ->
                           FStar_Tactics_Result.Failed (e1, ps'))))
                (FStar_Tactics_Types.decr_depth
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (516)) (Prims.of_int (26))
                                  (Prims.of_int (516)) (Prims.of_int (43))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (516)) (Prims.of_int (2))
                            (Prims.of_int (518)) (Prims.of_int (34))))))
and (deep_apply_subst_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun c ->
      fun subst ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (521)) (Prims.of_int (14))
                                 (Prims.of_int (521)) (Prims.of_int (51))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (522)) (Prims.of_int (2))
                           (Prims.of_int (545)) (Prims.of_int (49)))))
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
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (521))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (521))
                                                  (Prims.of_int (51))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (522))
                                            (Prims.of_int (2))
                                            (Prims.of_int (545))
                                            (Prims.of_int (49))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (523)) (Prims.of_int (4))
                                      (Prims.of_int (526))
                                      (Prims.of_int (34))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (528)) (Prims.of_int (2))
                                (Prims.of_int (545)) (Prims.of_int (49)))))
               with
               | true ->
                   ((match FStar_Reflection_Builtins.inspect_comp c with
                     | FStar_Reflection_Data.C_Total (ret, decr) ->
                         (fun ps1 ->
                            match (deep_apply_subst e ret subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (530))
                                                (Prims.of_int (14))
                                                (Prims.of_int (530))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (531))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (532))
                                                  (Prims.of_int (32)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun x ->
                                                  deep_apply_subst e x subst)
                                               decr)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (531))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (532))
                                                                (Prims.of_int (32))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (531))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (531))
                                                          (Prims.of_int (29))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (532))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (532))
                                                            (Prims.of_int (32)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_Total
                                                        (a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (532))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (532))
                                                               (Prims.of_int (32))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_GTotal (ret, decr) ->
                         (fun ps1 ->
                            match (deep_apply_subst e ret subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (534))
                                                (Prims.of_int (14))
                                                (Prims.of_int (534))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (535))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (536))
                                                  (Prims.of_int (33)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun x ->
                                                  deep_apply_subst e x subst)
                                               decr)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (535))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (536))
                                                                (Prims.of_int (33))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (535))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (535))
                                                          (Prims.of_int (29))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (536))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (536))
                                                            (Prims.of_int (33)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_GTotal
                                                        (a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (536))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (536))
                                                               (Prims.of_int (33))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_Lemma (pre, post, patterns) ->
                         (fun ps1 ->
                            match (deep_apply_subst e pre subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (538))
                                                (Prims.of_int (14))
                                                (Prims.of_int (538))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (539))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (541))
                                                  (Prims.of_int (41)))))
                                 with
                                 | true ->
                                     (match (deep_apply_subst e post subst)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (539))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (541))
                                                                (Prims.of_int (41))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (539))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (539))
                                                          (Prims.of_int (25))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (540))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (541))
                                                            (Prims.of_int (41)))))
                                           with
                                           | true ->
                                               (match (deep_apply_subst e
                                                         patterns subst)
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (41))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (33))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a2, ps'2) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (41)))))
                                                     with
                                                     | true ->
                                                         FStar_Tactics_Result.Success
                                                           ((FStar_Reflection_Builtins.pack_comp
                                                               (FStar_Reflection_Data.C_Lemma
                                                                  (a, a1, a2))),
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (41))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e1, ps'2) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e1, ps'2)))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))
                     | FStar_Reflection_Data.C_Eff
                         (us, eff_name, result, eff_args) ->
                         (fun ps1 ->
                            match (deep_apply_subst e result subst)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (543))
                                                (Prims.of_int (17))
                                                (Prims.of_int (543))
                                                (Prims.of_int (29))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (544))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (545))
                                                  (Prims.of_int (49)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Util.map
                                               (fun uu___ ->
                                                  match uu___ with
                                                  | (x, a1) ->
                                                      (fun ps2 ->
                                                         match (deep_apply_subst
                                                                  e x subst)
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (46))))))
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a2, ps'1) ->
                                                             (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (66)))))
                                                              with
                                                              | true ->
                                                                  (match 
                                                                    (match a1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Implicit
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a1, s))
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Explicit
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a1, s))
                                                                    | 
                                                                    FStar_Reflection_Data.Q_Meta
                                                                    t ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (deep_apply_subst
                                                                    e t subst)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (34))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Data.Q_Meta
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (34))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (65))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (66)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2, a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (66))))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)))
                                                         | FStar_Tactics_Result.Failed
                                                             (e1, ps'1) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e1, ps'1)))
                                               eff_args)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (544))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (545))
                                                                (Prims.of_int (49))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (544))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (544))
                                                          (Prims.of_int (76))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (545))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (545))
                                                            (Prims.of_int (49)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((FStar_Reflection_Builtins.pack_comp
                                                     (FStar_Reflection_Data.C_Eff
                                                        (us, eff_name, a, a1))),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (545))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (545))
                                                               (Prims.of_int (49))))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'1) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'1)))
                            | FStar_Tactics_Result.Failed (e1, ps') ->
                                FStar_Tactics_Result.Failed (e1, ps'))))
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
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (521))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (521))
                                                   (Prims.of_int (51))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (522))
                                             (Prims.of_int (2))
                                             (Prims.of_int (545))
                                             (Prims.of_int (49))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                       (Prims.of_int (523))
                                       (Prims.of_int (4))
                                       (Prims.of_int (526))
                                       (Prims.of_int (34))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (528)) (Prims.of_int (2))
                                 (Prims.of_int (545)) (Prims.of_int (49)))))))
and (deep_apply_subst_in_pattern :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Data.pattern ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          (FStar_Reflection_Data.pattern * (FStar_Reflection_Types.bv *
            FStar_Reflection_Types.term) Prims.list)
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun pat ->
      fun subst ->
        match pat with
        | FStar_Reflection_Data.Pat_Constant uu___ ->
            (fun s -> FStar_Tactics_Result.Success ((pat, subst), s))
        | FStar_Reflection_Data.Pat_Cons (fv, patterns) ->
            (fun ps ->
               match (FStar_Tactics_Util.fold_right
                        (fun uu___ ->
                           fun uu___1 ->
                             match (uu___, uu___1) with
                             | ((pat1, b), (pats, subst1)) ->
                                 (fun ps1 ->
                                    match (deep_apply_subst_in_pattern e pat1
                                             subst1)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (555))
                                                        (Prims.of_int (39))
                                                        (Prims.of_int (555))
                                                        (Prims.of_int (78))))))
                                    with
                                    | FStar_Tactics_Result.Success (a, ps')
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (555))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (555))
                                                          (Prims.of_int (36)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               (((match a with
                                                  | (pat2, subst2) ->
                                                      (((pat2, b) :: pats),
                                                        subst2))),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (555))
                                                             (Prims.of_int (26))
                                                             (Prims.of_int (555))
                                                             (Prims.of_int (36))))))))
                                    | FStar_Tactics_Result.Failed (e1, ps')
                                        ->
                                        FStar_Tactics_Result.Failed (e1, ps')))
                        patterns ([], subst))
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (554)) (Prims.of_int (6))
                                   (Prims.of_int (556)) (Prims.of_int (69))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (553)) (Prims.of_int (4))
                                     (Prims.of_int (558)) (Prims.of_int (31)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          (((match a with
                             | (patterns1, subst1) ->
                                 ((FStar_Reflection_Data.Pat_Cons
                                     (fv, patterns1)), subst1))),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (553))
                                        (Prims.of_int (4))
                                        (Prims.of_int (558))
                                        (Prims.of_int (31))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
        | FStar_Reflection_Data.Pat_Var bv ->
            (fun ps ->
               match (deep_apply_subst_in_bv e bv subst)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (560)) (Prims.of_int (20))
                                   (Prims.of_int (560)) (Prims.of_int (53))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (560)) (Prims.of_int (4))
                                     (Prims.of_int (561)) (Prims.of_int (21)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          (((match a with
                             | (bv1, subst1) ->
                                 ((FStar_Reflection_Data.Pat_Var bv1),
                                   subst1))),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (560))
                                        (Prims.of_int (4))
                                        (Prims.of_int (561))
                                        (Prims.of_int (21))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
        | FStar_Reflection_Data.Pat_Wild bv ->
            (fun ps ->
               match (deep_apply_subst_in_bv e bv subst)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (563)) (Prims.of_int (20))
                                   (Prims.of_int (563)) (Prims.of_int (53))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (563)) (Prims.of_int (4))
                                     (Prims.of_int (564)) (Prims.of_int (22)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          (((match a with
                             | (bv1, subst1) ->
                                 ((FStar_Reflection_Data.Pat_Wild bv1),
                                   subst1))),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (563))
                                        (Prims.of_int (4))
                                        (Prims.of_int (564))
                                        (Prims.of_int (22))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
        | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
            (fun ps ->
               match (deep_apply_subst_in_bv e bv subst)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (566)) (Prims.of_int (20))
                                   (Prims.of_int (566)) (Prims.of_int (53))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (566)) (Prims.of_int (4))
                                     (Prims.of_int (568)) (Prims.of_int (28)))))
                    with
                    | true ->
                        ((match a with
                          | (bv1, subst1) ->
                              (fun ps1 ->
                                 match (deep_apply_subst e t subst1)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (38))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                                       (Prims.of_int (568))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (568))
                                                       (Prims.of_int (28)))))
                                      with
                                      | true ->
                                          FStar_Tactics_Result.Success
                                            (((FStar_Reflection_Data.Pat_Dot_Term
                                                 (bv1, a1)), subst1),
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (568))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (568))
                                                          (Prims.of_int (28))))))))
                                 | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                     FStar_Tactics_Result.Failed (e1, ps'1))))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (566)) (Prims.of_int (4))
                                      (Prims.of_int (568))
                                      (Prims.of_int (28)))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
let (apply_subst :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  = norm_apply_subst
let (apply_subst_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  = norm_apply_subst_in_comp
let (opt_apply_subst :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
      (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun e ->
    fun opt_t ->
      fun subst ->
        match opt_t with
        | FStar_Pervasives_Native.None ->
            (fun s ->
               FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
        | FStar_Pervasives_Native.Some t ->
            (fun ps ->
               match (apply_subst e t subst)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (584)) (Prims.of_int (19))
                                   (Prims.of_int (584)) (Prims.of_int (42))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (584)) (Prims.of_int (14))
                                     (Prims.of_int (584)) (Prims.of_int (42)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Pervasives_Native.Some a),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (584))
                                        (Prims.of_int (14))
                                        (Prims.of_int (584))
                                        (Prims.of_int (42))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
let rec (_generate_shadowed_subst :
  genv ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.bv Prims.list ->
        FStar_Tactics_Types.proofstate ->
          (genv * (FStar_Reflection_Types.bv * FStar_Reflection_Types.bv)
            Prims.list) FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun t ->
      fun bvl ->
        match bvl with
        | [] -> (fun s -> FStar_Tactics_Result.Success ((ge, []), s))
        | old_bv::bvl' ->
            (fun ps ->
               match (FStar_Tactics_Builtins.inspect t)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                   (Prims.of_int (603)) (Prims.of_int (10))
                                   (Prims.of_int (603)) (Prims.of_int (19))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (603)) (Prims.of_int (4))
                                     (Prims.of_int (617)) (Prims.of_int (55)))))
                    with
                    | true ->
                        ((match a with
                          | FStar_Reflection_Data.Tv_Abs (b, uu___) ->
                              (fun ps1 ->
                                 match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (18))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (34))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (616))
                                                  (Prims.of_int (34)))))
                                 with
                                 | true ->
                                     ((match FStar_Reflection_Builtins.inspect_binder
                                               b
                                       with
                                       | (bv, uu___1) ->
                                           (fun ps2 ->
                                              match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (29))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (608))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (616))
                                                               (Prims.of_int (34)))))
                                              with
                                              | true ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (26))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
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
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (30))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
                                                        with
                                                        | true ->
                                                            (match (genv_push_fresh_bv
                                                                    ge
                                                                    (Prims.strcat
                                                                    "__"
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_ppname)
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_sort)
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (61))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a1, ps'1)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
                                                                  with
                                                                  | true ->
                                                                    ((match a1
                                                                    with
                                                                    | (ge1,
                                                                    fresh) ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    fresh))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (46))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.mk_e_app
                                                                    t a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (47))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    ge1.env
                                                                    [] a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (42))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (_generate_shadowed_subst
                                                                    ge1 a3
                                                                    bvl')
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (58))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a4
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    nbvl) ->
                                                                    (ge2,
                                                                    ((old_bv,
                                                                    fresh) ::
                                                                    nbvl)))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34))))))))
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
                                                                    (e, ps'3)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (610))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (34)))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'1) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'1)))))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Base.fst"
                                                         (Prims.of_int (606))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (606))
                                                         (Prims.of_int (34))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (616))
                                                   (Prims.of_int (34)))))))
                          | uu___ ->
                              mfail "_subst_with_fresh_vars: not a Tv_Abs"))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (603)) (Prims.of_int (4))
                                      (Prims.of_int (617))
                                      (Prims.of_int (55)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let (generate_shadowed_subst :
  genv ->
    FStar_Tactics_Types.proofstate ->
      (genv * (FStar_Reflection_Types.bv * FStar_Reflection_Types.bv)
        Prims.list) FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.Base.fst"
                             (Prims.of_int (621)) (Prims.of_int (12))
                             (Prims.of_int (621)) (Prims.of_int (33))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range
                       "experimental/FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (622)) (Prims.of_int (2))
                       (Prims.of_int (624)) (Prims.of_int (39)))))
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
                                              "experimental/FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (621))
                                              (Prims.of_int (12))
                                              (Prims.of_int (621))
                                              (Prims.of_int (33))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (622))
                                        (Prims.of_int (2))
                                        (Prims.of_int (624))
                                        (Prims.of_int (39))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (622)) (Prims.of_int (11))
                                  (Prims.of_int (622)) (Prims.of_int (37))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (623)) (Prims.of_int (2))
                            (Prims.of_int (624)) (Prims.of_int (39)))))
           with
           | true ->
               (match (FStar_Tactics_Derived.mk_abs
                         (FStar_List_Tot_Base.map
                            FStar_Reflection_Derived.mk_binder
                            (FStar_List_Tot_Base.rev ge.svars))
                         (FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_Const
                               FStar_Reflection_Data.C_Unit)))
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
                                                            "experimental/FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (621))
                                                            (Prims.of_int (12))
                                                            (Prims.of_int (621))
                                                            (Prims.of_int (33))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (622))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (624))
                                                      (Prims.of_int (39))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (622))
                                                (Prims.of_int (11))
                                                (Prims.of_int (622))
                                                (Prims.of_int (37))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.Base.fst"
                                          (Prims.of_int (623))
                                          (Prims.of_int (2))
                                          (Prims.of_int (624))
                                          (Prims.of_int (39))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (623)) (Prims.of_int (14))
                                    (Prims.of_int (623)) (Prims.of_int (29))))))
                with
                | FStar_Tactics_Result.Success (a, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (624)) (Prims.of_int (2))
                                      (Prims.of_int (624))
                                      (Prims.of_int (39)))))
                     with
                     | true ->
                         (_generate_shadowed_subst ge a
                            (FStar_List_Tot_Base.rev ge.svars))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Base.fst"
                                       (Prims.of_int (624))
                                       (Prims.of_int (2))
                                       (Prims.of_int (624))
                                       (Prims.of_int (39)))))))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))