open Prims
let (pure_effect_qn : Prims.string) = "Prims.PURE"
let (pure_hoare_effect_qn : Prims.string) = "Prims.Pure"
let (stack_effect_qn : Prims.string) = "FStar.HyperStack.ST.Stack"
let (st_effect_qn : Prims.string) = "FStar.HyperStack.ST.ST"
let (comp_qualifier :
  FStar_Reflection_Types.comp ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun c ->
    fun s ->
      FStar_Tactics_Result.Success
        ((match FStar_Reflection_Builtins.inspect_comp c with
          | FStar_Reflection_Data.C_Total (uu___, uu___1) -> "C_Total"
          | FStar_Reflection_Data.C_GTotal (uu___, uu___1) -> "C_GTotal"
          | FStar_Reflection_Data.C_Lemma (uu___, uu___1, uu___2) ->
              "C_Lemma"
          | FStar_Reflection_Data.C_Eff (uu___, uu___1, uu___2, uu___3) ->
              "C_Eff"), s)
type effect_type =
  | E_Total 
  | E_GTotal 
  | E_Lemma 
  | E_PURE 
  | E_Pure 
  | E_Stack 
  | E_ST 
  | E_Unknown 
let (uu___is_E_Total : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Total -> true | uu___ -> false
let (uu___is_E_GTotal : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_GTotal -> true | uu___ -> false
let (uu___is_E_Lemma : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Lemma -> true | uu___ -> false
let (uu___is_E_PURE : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_PURE -> true | uu___ -> false
let (uu___is_E_Pure : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Pure -> true | uu___ -> false
let (uu___is_E_Stack : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Stack -> true | uu___ -> false
let (uu___is_E_ST : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_ST -> true | uu___ -> false
let (uu___is_E_Unknown : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Unknown -> true | uu___ -> false
let (effect_type_to_string : effect_type -> Prims.string) =
  fun ety ->
    match ety with
    | E_Total -> "E_Total"
    | E_GTotal -> "E_GTotal"
    | E_Lemma -> "E_Lemma"
    | E_PURE -> "E_PURE"
    | E_Pure -> "E_Pure"
    | E_Stack -> "E_Stack"
    | E_ST -> "E_ST"
    | E_Unknown -> "E_Unknown"
let (effect_name_to_type : FStar_Reflection_Types.name -> effect_type) =
  fun ename ->
    let ename1 = FStar_Reflection_Derived.flatten_name ename in
    if ename1 = pure_effect_qn
    then E_PURE
    else
      if ename1 = pure_hoare_effect_qn
      then E_Pure
      else
        if ename1 = stack_effect_qn
        then E_Stack
        else if ename1 = st_effect_qn then E_ST else E_Unknown
let (effect_type_is_pure : effect_type -> Prims.bool) =
  fun etype ->
    match etype with
    | E_Total -> true
    | E_GTotal -> true
    | E_Lemma -> true
    | E_PURE -> true
    | E_Pure -> true
    | E_Stack -> false
    | E_ST -> false
    | E_Unknown -> false
type type_info =
  {
  ty: FStar_Reflection_Types.typ ;
  refin: FStar_Reflection_Types.term FStar_Pervasives_Native.option }
let (__proj__Mktype_info__item__ty : type_info -> FStar_Reflection_Types.typ)
  = fun projectee -> match projectee with | { ty; refin;_} -> ty
let (__proj__Mktype_info__item__refin :
  type_info -> FStar_Reflection_Types.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { ty; refin;_} -> refin
let (mk_type_info :
  FStar_Reflection_Types.typ ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option -> type_info)
  = fun uu___ -> fun uu___1 -> { ty = uu___; refin = uu___1 }
let (type_info_to_string : type_info -> Prims.string) =
  fun info ->
    Prims.strcat "Mktype_info ("
      (Prims.strcat (FStar_Reflection_Builtins.term_to_string info.ty)
         (Prims.strcat ") ("
            (Prims.strcat
               (FStar_InteractiveHelpers_Base.option_to_string
                  FStar_Reflection_Builtins.term_to_string info.refin) ")")))
let (unit_type_info : type_info) =
  mk_type_info
    (FStar_Reflection_Builtins.pack_ln
       (FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"])))
    FStar_Pervasives_Native.None
let (safe_tc :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Pervasives_Native.option
          FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               (fun ps ->
                  match (FStar_Tactics_Builtins.tc e t)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (91)) (Prims.of_int (11))
                                      (Prims.of_int (91)) (Prims.of_int (19))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (91))
                                        (Prims.of_int (6))
                                        (Prims.of_int (91))
                                        (Prims.of_int (19)))))
                       with
                       | true ->
                           FStar_Tactics_Result.Success
                             ((FStar_Pervasives_Native.Some a),
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (91))
                                           (Prims.of_int (6))
                                           (Prims.of_int (91))
                                           (Prims.of_int (19))))))))
                  | FStar_Tactics_Result.Failed (e1, ps') ->
                      FStar_Tactics_Result.Failed (e1, ps')))
        (fun uu___ ->
           fun s ->
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
let (safe_tcc :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.comp FStar_Pervasives_Native.option
          FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               (fun ps ->
                  match (FStar_Tactics_Builtins.tcc e t)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (95)) (Prims.of_int (11))
                                      (Prims.of_int (95)) (Prims.of_int (20))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (95))
                                        (Prims.of_int (6))
                                        (Prims.of_int (95))
                                        (Prims.of_int (20)))))
                       with
                       | true ->
                           FStar_Tactics_Result.Success
                             ((FStar_Pervasives_Native.Some a),
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (95))
                                           (Prims.of_int (6))
                                           (Prims.of_int (95))
                                           (Prims.of_int (20))))))))
                  | FStar_Tactics_Result.Failed (e1, ps') ->
                      FStar_Tactics_Result.Failed (e1, ps')))
        (fun uu___ ->
           fun s ->
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
let (get_type_info_from_type :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate -> type_info FStar_Tactics_Result.__result)
  =
  fun ty ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect ty)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (98)) (Prims.of_int (8))
                          (Prims.of_int (98)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (98)) (Prims.of_int (2))
                            (Prims.of_int (109)) (Prims.of_int (24)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_Refine (bv, refin) ->
                     (fun ps1 ->
                        match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (100))
                                               (Prims.of_int (26))
                                               (Prims.of_int (100))
                                               (Prims.of_int (39))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (101))
                                         (Prims.of_int (4))
                                         (Prims.of_int (106))
                                         (Prims.of_int (38)))))
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
                                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (100))
                                                                (Prims.of_int (26))
                                                                (Prims.of_int (100))
                                                                (Prims.of_int (39))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (101))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (106))
                                                          (Prims.of_int (38))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (101))
                                                    (Prims.of_int (25))
                                                    (Prims.of_int (101))
                                                    (Prims.of_int (38))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (102))
                                              (Prims.of_int (4))
                                              (Prims.of_int (106))
                                              (Prims.of_int (38)))))
                             with
                             | true ->
                                 (match (FStar_InteractiveHelpers_Base.prettify_term
                                           false
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
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (39))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (101))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (101))
                                                                  (Prims.of_int (38))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (102))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (106))
                                                            (Prims.of_int (38))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (47))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (103))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (106))
                                                        (Prims.of_int (38)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (103))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (103))
                                                                   (Prims.of_int (33))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (104))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (106))
                                                             (Prims.of_int (38)))))
                                            with
                                            | true ->
                                                (match (FStar_InteractiveHelpers_Base.prettify_term
                                                          false refin)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (41))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a2, ps'2) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38)))))
                                                      with
                                                      | true ->
                                                          (match (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Derived.mk_binder
                                                                    bv), a2)))
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (37))))))
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a3, ps'3) ->
                                                               (match 
                                                                  FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38)))))
                                                                with
                                                                | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((mk_type_info
                                                                    a1
                                                                    (FStar_Pervasives_Native.Some
                                                                    a3)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (38))))))))
                                                           | FStar_Tactics_Result.Failed
                                                               (e, ps'3) ->
                                                               FStar_Tactics_Result.Failed
                                                                 (e, ps'3)))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'2) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'2))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1))))
                 | uu___ ->
                     (fun ps1 ->
                        match (FStar_InteractiveHelpers_Base.prettify_term
                                 false ty)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (108))
                                            (Prims.of_int (13))
                                            (Prims.of_int (108))
                                            (Prims.of_int (35))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (109))
                                              (Prims.of_int (4))
                                              (Prims.of_int (109))
                                              (Prims.of_int (24)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   ((mk_type_info a1
                                       FStar_Pervasives_Native.None),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (109))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (109))
                                                 (Prims.of_int (24))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (98)) (Prims.of_int (2))
                             (Prims.of_int (109)) (Prims.of_int (24)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (get_type_info :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        type_info FStar_Pervasives_Native.option
          FStar_Tactics_Result.__result)
  =
  fun e ->
    fun t ->
      fun ps ->
        match (safe_tc e t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (113)) (Prims.of_int (8))
                            (Prims.of_int (113)) (Prims.of_int (19))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (113)) (Prims.of_int (2))
                              (Prims.of_int (115)) (Prims.of_int (48)))))
             with
             | true ->
                 ((match a with
                   | FStar_Pervasives_Native.None ->
                       (fun s ->
                          FStar_Tactics_Result.Success
                            (FStar_Pervasives_Native.None, s))
                   | FStar_Pervasives_Native.Some ty ->
                       (fun ps1 ->
                          match (get_type_info_from_type ty)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (115))
                                              (Prims.of_int (20))
                                              (Prims.of_int (115))
                                              (Prims.of_int (48))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (115))
                                                (Prims.of_int (15))
                                                (Prims.of_int (115))
                                                (Prims.of_int (48)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((FStar_Pervasives_Native.Some a1),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (115))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (115))
                                                   (Prims.of_int (48))))))))
                          | FStar_Tactics_Result.Failed (e1, ps'1) ->
                              FStar_Tactics_Result.Failed (e1, ps'1))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (113)) (Prims.of_int (2))
                               (Prims.of_int (115)) (Prims.of_int (48)))))))
        | FStar_Tactics_Result.Failed (e1, ps') ->
            FStar_Tactics_Result.Failed (e1, ps')
let (get_total_or_gtotal_ret_type :
  FStar_Reflection_Types.comp ->
    FStar_Reflection_Types.typ FStar_Pervasives_Native.option)
  =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total (ret_ty, uu___) ->
        FStar_Pervasives_Native.Some ret_ty
    | FStar_Reflection_Data.C_GTotal (ret_ty, uu___) ->
        FStar_Pervasives_Native.Some ret_ty
    | uu___ -> FStar_Pervasives_Native.None
let (get_comp_ret_type :
  FStar_Reflection_Types.comp -> FStar_Reflection_Types.typ) =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total (ret_ty, uu___) -> ret_ty
    | FStar_Reflection_Data.C_GTotal (ret_ty, uu___) -> ret_ty
    | FStar_Reflection_Data.C_Eff (uu___, uu___1, ret_ty, uu___2) -> ret_ty
    | FStar_Reflection_Data.C_Lemma (uu___, uu___1, uu___2) ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"]))
let (is_total_or_gtotal : FStar_Reflection_Types.comp -> Prims.bool) =
  fun c ->
    FStar_Pervasives_Native.uu___is_Some (get_total_or_gtotal_ret_type c)
let (is_unit_type :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun ty ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect ty)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (137)) (Prims.of_int (8))
                          (Prims.of_int (137)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (137)) (Prims.of_int (2))
                            (Prims.of_int (139)) (Prims.of_int (14)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((FStar_InteractiveHelpers_Base.fv_eq_name fv
                              FStar_Reflection_Const.unit_lid), s))
                 | uu___ ->
                     (fun s -> FStar_Tactics_Result.Success (false, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (137)) (Prims.of_int (2))
                             (Prims.of_int (139)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
type typ_or_comp =
  | TC_Typ of FStar_Reflection_Types.typ * FStar_Reflection_Types.binder
  Prims.list * Prims.nat 
  | TC_Comp of FStar_Reflection_Types.comp * FStar_Reflection_Types.binder
  Prims.list * Prims.nat 
let (uu___is_TC_Typ : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Typ (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Typ__item__v : typ_or_comp -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> v
let (__proj__TC_Typ__item__pl :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> pl
let (__proj__TC_Typ__item__num_unflushed : typ_or_comp -> Prims.nat) =
  fun projectee ->
    match projectee with | TC_Typ (v, pl, num_unflushed) -> num_unflushed
let (uu___is_TC_Comp : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Comp (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Comp__item__v : typ_or_comp -> FStar_Reflection_Types.comp) =
  fun projectee -> match projectee with | TC_Comp (v, pl, num_unflushed) -> v
let (__proj__TC_Comp__item__pl :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
  fun projectee ->
    match projectee with | TC_Comp (v, pl, num_unflushed) -> pl
let (__proj__TC_Comp__item__num_unflushed : typ_or_comp -> Prims.nat) =
  fun projectee ->
    match projectee with | TC_Comp (v, pl, num_unflushed) -> num_unflushed
let (typ_or_comp_to_string : typ_or_comp -> Prims.string) =
  fun tyc ->
    match tyc with
    | TC_Typ (v, pl, num_unflushed) ->
        Prims.strcat "TC_Typ ("
          (Prims.strcat (FStar_Reflection_Builtins.term_to_string v)
             (Prims.strcat ") "
                (Prims.strcat
                   (FStar_InteractiveHelpers_Base.list_to_string
                      FStar_Reflection_Derived.name_of_binder pl)
                   (Prims.strcat " " (Prims.string_of_int num_unflushed)))))
    | TC_Comp (c, pl, num_unflushed) ->
        Prims.strcat "TC_Comp ("
          (Prims.strcat (FStar_InteractiveHelpers_Base.acomp_to_string c)
             (Prims.strcat ") "
                (Prims.strcat
                   (FStar_InteractiveHelpers_Base.list_to_string
                      FStar_Reflection_Derived.name_of_binder pl)
                   (Prims.strcat " " (Prims.string_of_int num_unflushed)))))
let (params_of_typ_or_comp :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
  fun c ->
    match c with
    | TC_Typ (uu___, pl, uu___1) -> pl
    | TC_Comp (uu___, pl, uu___1) -> pl
let (num_unflushed_of_typ_or_comp : typ_or_comp -> Prims.nat) =
  fun c ->
    match c with
    | TC_Typ (uu___, uu___1, n) -> n
    | TC_Comp (uu___, uu___1, n) -> n
let (safe_typ_or_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          typ_or_comp FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun e ->
      fun t ->
        fun ps ->
          match (safe_tcc e t)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (185)) (Prims.of_int (8))
                              (Prims.of_int (185)) (Prims.of_int (20))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (185)) (Prims.of_int (2))
                                (Prims.of_int (195)) (Prims.of_int (25)))))
               with
               | true ->
                   ((match a with
                     | FStar_Pervasives_Native.None ->
                         (fun ps1 ->
                            match (FStar_InteractiveHelpers_Base.print_dbg
                                     dbg
                                     (Prims.strcat "[> safe_typ_or_comp:"
                                        (Prims.strcat "\n-term: "
                                           (Prims.strcat
                                              (FStar_Reflection_Builtins.term_to_string
                                                 t) "\n-comp: None"))))
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (187))
                                                (Prims.of_int (4))
                                                (Prims.of_int (189))
                                                (Prims.of_int (35))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (190))
                                                  (Prims.of_int (8)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       (FStar_Pervasives_Native.None,
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (190))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (190))
                                                     (Prims.of_int (8))))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))
                     | FStar_Pervasives_Native.Some c ->
                         (fun ps1 ->
                            match (FStar_InteractiveHelpers_Base.print_dbg
                                     dbg
                                     (Prims.strcat "[> safe_typ_or_comp:"
                                        (Prims.strcat "\n-term: "
                                           (Prims.strcat
                                              (FStar_Reflection_Builtins.term_to_string
                                                 t)
                                              (Prims.strcat "\n-comp: "
                                                 (FStar_InteractiveHelpers_Base.acomp_to_string
                                                    c))))))
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (192))
                                                (Prims.of_int (4))
                                                (Prims.of_int (194))
                                                (Prims.of_int (51))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (195))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (195))
                                                  (Prims.of_int (25)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       ((FStar_Pervasives_Native.Some
                                           (TC_Comp (c, [], Prims.int_zero))),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (195))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (195))
                                                     (Prims.of_int (25))))))))
                            | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                FStar_Tactics_Result.Failed (e1, ps'1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (185)) (Prims.of_int (2))
                                 (Prims.of_int (195)) (Prims.of_int (25)))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (subst_bv_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.bv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.comp ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun b ->
      fun t ->
        fun c ->
          FStar_InteractiveHelpers_Base.apply_subst_in_comp e c [(b, t)]
let (subst_binder_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.binder ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.comp ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun b ->
      fun t ->
        fun c ->
          subst_bv_in_comp e (FStar_Reflection_Derived.bv_of_binder b) t c
let rec (unfold_until_arrow :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.typ ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.typ FStar_Tactics_Result.__result)
  =
  fun e ->
    fun ty0 ->
      fun ps ->
        match match (FStar_Tactics_Builtins.inspect ty0)
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (209))
                                        (Prims.of_int (5))
                                        (Prims.of_int (209))
                                        (Prims.of_int (28))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (209)) (Prims.of_int (15))
                                  (Prims.of_int (209)) (Prims.of_int (28))))))
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (209)) (Prims.of_int (5))
                                    (Prims.of_int (209)) (Prims.of_int (28)))))
                   with
                   | true ->
                       FStar_Tactics_Result.Success
                         ((FStar_Reflection_Data.uu___is_Tv_Arrow a),
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (209))
                                       (Prims.of_int (5))
                                       (Prims.of_int (209))
                                       (Prims.of_int (28))))))))
              | FStar_Tactics_Result.Failed (e1, ps') ->
                  FStar_Tactics_Result.Failed (e1, ps')
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (209)) (Prims.of_int (2))
                              (Prims.of_int (255)) (Prims.of_int (7)))))
             with
             | true ->
                 (if a
                  then (fun s -> FStar_Tactics_Result.Success (ty0, s))
                  else
                    (fun ps1 ->
                       match (FStar_Tactics_Builtins.norm_term_env e [] ty0)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (213))
                                           (Prims.of_int (13))
                                           (Prims.of_int (213))
                                           (Prims.of_int (35))))))
                       with
                       | FStar_Tactics_Result.Success (a1, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (215))
                                             (Prims.of_int (4))
                                             (Prims.of_int (254))
                                             (Prims.of_int (75)))))
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
                                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (215))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (254))
                                                              (Prims.of_int (75))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (216))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (226))
                                                        (Prims.of_int (9))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (229))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (254))
                                                  (Prims.of_int (75)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Builtins.inspect
                                               a1)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (75))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (229))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (254))
                                                                (Prims.of_int (75))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (229))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (229))
                                                          (Prims.of_int (20))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (229))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (254))
                                                            (Prims.of_int (75)))))
                                           with
                                           | true ->
                                               ((match a2 with
                                                 | FStar_Reflection_Data.Tv_Arrow
                                                     (uu___1, uu___2) ->
                                                     (fun s ->
                                                        FStar_Tactics_Result.Success
                                                          (a1, s))
                                                 | FStar_Reflection_Data.Tv_FVar
                                                     fv ->
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (32))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a3, ps'3)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9)))))
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
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    e
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)]] a3)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (53))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    a4)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    fv' ->
                                                                    if
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv')) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv))
                                                                    then
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    (Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    ty0))
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a4, s))
                                                                    | uu___1
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a4, s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e1, ps'3)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a3, ps'3) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (30)))))
                                                             with
                                                             | true ->
                                                                 (unfold_until_arrow
                                                                    e a3)
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (30)))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e1, ps'3) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e1, ps'3))
                                                 | FStar_Reflection_Data.Tv_App
                                                     (uu___1, uu___2) ->
                                                     (fun ps2 ->
                                                        match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (35))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (9)))))
                                                        with
                                                        | true ->
                                                            ((match FStar_Reflection_Derived.collect_app
                                                                    a1
                                                              with
                                                              | (hd, args) ->
                                                                  (fun ps3 ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    hd)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (28))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (82)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (32))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9)))))
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
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    e
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)]] a4)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (53))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    a5)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'6) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a6
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    fv' ->
                                                                    if
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv')) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv))
                                                                    then
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    (Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    ty0))
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a5, s))
                                                                    | uu___3
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a5, s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (29)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'6) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'6)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4)
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (32)))))
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
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (32)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (unfold_until_arrow
                                                                    e
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    a4 args))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (32))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4))
                                                                    | uu___3
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    (Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    ty0))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (82)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3))))
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (35))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (9)))))))
                                                 | FStar_Reflection_Data.Tv_Refine
                                                     (bv, ref) ->
                                                     (fun ps2 ->
                                                        match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (29))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (30)))))
                                                        with
                                                        | true ->
                                                            (unfold_until_arrow
                                                               e
                                                               (FStar_Reflection_Derived.type_of_bv
                                                                  bv))
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (29))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Reflection_Data.Tv_AscribedT
                                                     (body, uu___1, uu___2)
                                                     ->
                                                     unfold_until_arrow e
                                                       body
                                                 | FStar_Reflection_Data.Tv_AscribedC
                                                     (body, uu___1, uu___2)
                                                     ->
                                                     unfold_until_arrow e
                                                       body
                                                 | uu___1 ->
                                                     FStar_InteractiveHelpers_Base.mfail
                                                       (Prims.strcat
                                                          "unfold_until_arrow: could not unfold: "
                                                          (FStar_Reflection_Builtins.term_to_string
                                                             ty0))))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (229))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (254))
                                                             (Prims.of_int (75)))))))
                                      | FStar_Tactics_Result.Failed
                                          (e1, ps'2) ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps'2))))
                       | FStar_Tactics_Result.Failed (e1, ps'1) ->
                           FStar_Tactics_Result.Failed (e1, ps'1)))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (209)) (Prims.of_int (2))
                               (Prims.of_int (255)) (Prims.of_int (7)))))))
        | FStar_Tactics_Result.Failed (e1, ps') ->
            FStar_Tactics_Result.Failed (e1, ps')
let (inst_comp_once :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun c ->
      fun t ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (260)) (Prims.of_int (11))
                                 (Prims.of_int (260)) (Prims.of_int (30))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (261)) (Prims.of_int (2))
                           (Prims.of_int (267)) (Prims.of_int (5)))))
          with
          | true ->
              (match (unfold_until_arrow e (get_comp_ret_type c))
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (260))
                                               (Prims.of_int (11))
                                               (Prims.of_int (260))
                                               (Prims.of_int (30))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (261))
                                         (Prims.of_int (2))
                                         (Prims.of_int (267))
                                         (Prims.of_int (5))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (261)) (Prims.of_int (12))
                                   (Prims.of_int (261)) (Prims.of_int (35))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (262)) (Prims.of_int (8))
                                     (Prims.of_int (266)) (Prims.of_int (46)))))
                    with
                    | true ->
                        (match (FStar_Tactics_Builtins.inspect a)
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (262))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (266))
                                                   (Prims.of_int (46))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (262))
                                             (Prims.of_int (14))
                                             (Prims.of_int (262))
                                             (Prims.of_int (25))))))
                         with
                         | FStar_Tactics_Result.Success (a1, ps'1) ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (262))
                                               (Prims.of_int (8))
                                               (Prims.of_int (266))
                                               (Prims.of_int (46)))))
                              with
                              | true ->
                                  ((match a1 with
                                    | FStar_Reflection_Data.Tv_Arrow 
                                        (b1, c1) ->
                                        subst_binder_in_comp e b1 t c1
                                    | uu___ ->
                                        FStar_InteractiveHelpers_Base.mfail
                                          "inst_comp_once: inconsistent state"))
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (262))
                                                (Prims.of_int (8))
                                                (Prims.of_int (266))
                                                (Prims.of_int (46)))))))
                         | FStar_Tactics_Result.Failed (e1, ps'1) ->
                             FStar_Tactics_Result.Failed (e1, ps'1)))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
let rec (inst_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      FStar_Reflection_Types.term Prims.list ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun e ->
    fun c ->
      fun tl ->
        match tl with
        | [] -> (fun s -> FStar_Tactics_Result.Success (c, s))
        | t::tl' ->
            (fun ps ->
               match (FStar_Tactics_Derived.try_with
                        (fun uu___ ->
                           match () with | () -> inst_comp_once e c t)
                        (fun uu___ ->
                           match uu___ with
                           | FStar_InteractiveHelpers_Base.MetaAnalysis msg
                               ->
                               FStar_InteractiveHelpers_Base.mfail
                                 (Prims.strcat "inst_comp: error: " msg)
                           | err -> FStar_Tactics_Effect.raise err))
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (274)) (Prims.of_int (13))
                                   (Prims.of_int (276)) (Prims.of_int (36))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (278)) (Prims.of_int (4))
                                     (Prims.of_int (278)) (Prims.of_int (22)))))
                    with
                    | true ->
                        (inst_comp e a tl')
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (278)) (Prims.of_int (4))
                                      (Prims.of_int (278))
                                      (Prims.of_int (22)))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
let (_abs_update_typ :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.typ ->
      FStar_Reflection_Types.binder Prims.list ->
        FStar_Reflection_Types.env ->
          FStar_Tactics_Types.proofstate ->
            typ_or_comp FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ty ->
      fun pl ->
        fun e ->
          FStar_Tactics_Derived.try_with
            (fun uu___ ->
               match () with
               | () ->
                   (fun ps ->
                      match (unfold_until_arrow e ty)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (293))
                                          (Prims.of_int (14))
                                          (Prims.of_int (293))
                                          (Prims.of_int (37))))))
                      with
                      | FStar_Tactics_Result.Success (a, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (294))
                                            (Prims.of_int (10))
                                            (Prims.of_int (299))
                                            (Prims.of_int (49)))))
                           with
                           | true ->
                               (match (FStar_Tactics_Builtins.inspect a)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (294))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (299))
                                                          (Prims.of_int (49))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (294))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (294))
                                                    (Prims.of_int (27))))))
                                with
                                | FStar_Tactics_Result.Success (a1, ps'1) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (294))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (299))
                                                      (Prims.of_int (49)))))
                                     with
                                     | true ->
                                         ((match a1 with
                                           | FStar_Reflection_Data.Tv_Arrow
                                               (b1, c1) ->
                                               (fun ps1 ->
                                                  match match (FStar_Tactics_Builtins.pack
                                                                 (FStar_Reflection_Data.Tv_Var
                                                                    (
                                                                    FStar_Reflection_Derived.bv_of_binder
                                                                    b)))
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (77))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (74))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a2, ps'2) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (77)))))
                                                             with
                                                             | true ->
                                                                 (subst_binder_in_comp
                                                                    e b1 a2
                                                                    c1)
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (77)))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (29)))))
                                                       with
                                                       | true ->
                                                           FStar_Tactics_Result.Success
                                                             ((TC_Comp
                                                                 (a2, (b ::
                                                                   pl),
                                                                   Prims.int_zero)),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (29))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e1, ps'2) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e1, ps'2))
                                           | uu___1 ->
                                               FStar_InteractiveHelpers_Base.mfail
                                                 "_abs_update_typ: inconsistent state"))
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (294))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (299))
                                                       (Prims.of_int (49)))))))
                                | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                    FStar_Tactics_Result.Failed (e1, ps'1)))
                      | FStar_Tactics_Result.Failed (e1, ps') ->
                          FStar_Tactics_Result.Failed (e1, ps')))
            (fun uu___ ->
               match uu___ with
               | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                   FStar_InteractiveHelpers_Base.mfail
                     (Prims.strcat
                        "_abs_update_typ: could not find an arrow in: "
                        (Prims.strcat
                           (FStar_Reflection_Builtins.term_to_string ty)
                           (Prims.strcat ":\n" msg)))
               | err -> FStar_Tactics_Effect.raise err)
let (abs_update_typ_or_comp :
  FStar_Reflection_Types.binder ->
    typ_or_comp ->
      FStar_Reflection_Types.env ->
        FStar_Tactics_Types.proofstate ->
          typ_or_comp FStar_Tactics_Result.__result)
  =
  fun b ->
    fun c ->
      fun e ->
        fun s ->
          FStar_Tactics_Result.Success
            ((match c with
              | TC_Typ (v, pl, n) ->
                  TC_Typ (v, (b :: pl), (n + Prims.int_one))
              | TC_Comp (v, pl, n) ->
                  TC_Comp (v, (b :: pl), (n + Prims.int_one))), s)
let (abs_update_opt_typ_or_comp :
  FStar_Reflection_Types.binder ->
    typ_or_comp FStar_Pervasives_Native.option ->
      FStar_Reflection_Types.env ->
        FStar_Tactics_Types.proofstate ->
          typ_or_comp FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun b ->
    fun opt_c ->
      fun e ->
        match opt_c with
        | FStar_Pervasives_Native.None ->
            (fun s ->
               FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
        | FStar_Pervasives_Native.Some c ->
            FStar_Tactics_Derived.try_with
              (fun uu___ ->
                 match () with
                 | () ->
                     (fun ps ->
                        match (abs_update_typ_or_comp b c e)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (325))
                                            (Prims.of_int (14))
                                            (Prims.of_int (325))
                                            (Prims.of_int (42))))))
                        with
                        | FStar_Tactics_Result.Success (a, ps') ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (326))
                                              (Prims.of_int (6))
                                              (Prims.of_int (326))
                                              (Prims.of_int (12)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   ((FStar_Pervasives_Native.Some a),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (326))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (326))
                                                 (Prims.of_int (12))))))))
                        | FStar_Tactics_Result.Failed (e1, ps') ->
                            FStar_Tactics_Result.Failed (e1, ps')))
              (fun uu___ ->
                 match uu___ with
                 | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          (FStar_Pervasives_Native.None, s))
                 | err -> FStar_Tactics_Effect.raise err)
let rec (_flush_typ_or_comp_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.binder Prims.list ->
        (FStar_Reflection_Types.bv * FStar_Reflection_Types.term) Prims.list
          ->
          FStar_Reflection_Types.comp ->
            FStar_Tactics_Types.proofstate ->
              FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun e ->
      fun rem ->
        fun inst ->
          fun c ->
            fun ps ->
              match FStar_Tactics_Types.tracepoint
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (343)) (Prims.of_int (4))
                                     (Prims.of_int (344)) (Prims.of_int (32))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (346)) (Prims.of_int (2))
                               (Prims.of_int (363)) (Prims.of_int (73)))))
              with
              | true ->
                  ((match rem with
                    | [] ->
                        (fun ps1 ->
                           match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (343))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (343))
                                                  (Prims.of_int (28))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (344))
                                            (Prims.of_int (4))
                                            (Prims.of_int (344))
                                            (Prims.of_int (32)))))
                           with
                           | true ->
                               (FStar_InteractiveHelpers_Base.apply_subst_in_comp
                                  e c (FStar_List_Tot_Base.rev inst))
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (343))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (343))
                                                   (Prims.of_int (28))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (344))
                                             (Prims.of_int (4))
                                             (Prims.of_int (344))
                                             (Prims.of_int (32)))))))
                    | b::rem' ->
                        (fun ps1 ->
                           match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (352))
                                                  (Prims.of_int (13))
                                                  (Prims.of_int (352))
                                                  (Prims.of_int (32))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (353))
                                            (Prims.of_int (4))
                                            (Prims.of_int (363))
                                            (Prims.of_int (73)))))
                           with
                           | true ->
                               (match match match (FStar_Tactics_Builtins.inspect
                                                     (get_comp_ret_type c))
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (47))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (31))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (31))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a, ps') ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (9))
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (31)))))
                                                 with
                                                 | true ->
                                                     FStar_Tactics_Result.Success
                                                       ((FStar_Reflection_Data.uu___is_Tv_Arrow
                                                           a),
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (31))))))))
                                            | FStar_Tactics_Result.Failed
                                                (e1, ps') ->
                                                FStar_Tactics_Result.Failed
                                                  (e1, ps')
                                      with
                                      | FStar_Tactics_Result.Success 
                                          (a, ps') ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (354))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (355))
                                                            (Prims.of_int (47)))))
                                           with
                                           | true ->
                                               (if a
                                                then
                                                  (fun s ->
                                                     FStar_Tactics_Result.Success
                                                       (((get_comp_ret_type c),
                                                          inst), s))
                                                else
                                                  (fun ps2 ->
                                                     match match match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (32)))))
                                                                 with
                                                                 | true ->
                                                                    (FStar_InteractiveHelpers_Base.apply_subst_in_comp
                                                                    e c
                                                                    (FStar_List_Tot_Base.rev
                                                                    inst))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (32))))))
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a1, ps'1) ->
                                                               (match 
                                                                  FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43)))))
                                                                with
                                                                | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((get_comp_ret_type
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))))))))
                                                           | FStar_Tactics_Result.Failed
                                                               (e1, ps'1) ->
                                                               FStar_Tactics_Result.Failed
                                                                 (e1, ps'1)
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a1, ps'1) ->
                                                         (match FStar_Tactics_Types.tracepoint
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (47)))))
                                                          with
                                                          | true ->
                                                              FStar_Tactics_Result.Success
                                                                ((a1, []),
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (47))))))))
                                                     | FStar_Tactics_Result.Failed
                                                         (e1, ps'1) ->
                                                         FStar_Tactics_Result.Failed
                                                           (e1, ps'1)))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (354))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (355))
                                                             (Prims.of_int (47)))))))
                                      | FStar_Tactics_Result.Failed (e1, ps')
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e1, ps')
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (353))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (363))
                                                      (Prims.of_int (73)))))
                                     with
                                     | true ->
                                         ((match a with
                                           | (ty, inst') ->
                                               (fun ps2 ->
                                                  match (FStar_Tactics_Builtins.inspect
                                                           ty)
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (20))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a1, ps'1) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (73)))))
                                                       with
                                                       | true ->
                                                           ((match a1 with
                                                             | FStar_Reflection_Data.Tv_Arrow
                                                                 (b', c') ->
                                                                 (fun ps3 ->
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    (FStar_Reflection_Derived.bv_of_binder
                                                                    b)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (98))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (91))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (90))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (91)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((FStar_Reflection_Derived.bv_of_binder
                                                                    b'), a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (91))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (98)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2 ::
                                                                    inst),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (98))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (101)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (_flush_typ_or_comp_comp
                                                                    dbg e
                                                                    rem' a2
                                                                    c')
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (101)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2))
                                                             | uu___ ->
                                                                 FStar_InteractiveHelpers_Base.mfail
                                                                   (Prims.strcat
                                                                    "_flush_typ_or_comp: inconsistent state"
                                                                    (Prims.strcat
                                                                    "\n-comp: "
                                                                    (Prims.strcat
                                                                    (FStar_InteractiveHelpers_Base.acomp_to_string
                                                                    c)
                                                                    (Prims.strcat
                                                                    "\n-remaning binders: "
                                                                    (FStar_InteractiveHelpers_Base.list_to_string
                                                                    FStar_Reflection_Derived.name_of_binder
                                                                    rem)))))))
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (73)))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e1, ps'1) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e1, ps'1))))
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (353))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (363))
                                                       (Prims.of_int (73)))))))
                                | FStar_Tactics_Result.Failed (e1, ps') ->
                                    FStar_Tactics_Result.Failed (e1, ps')))))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (343)) (Prims.of_int (4))
                                      (Prims.of_int (344))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (346)) (Prims.of_int (2))
                                (Prims.of_int (363)) (Prims.of_int (73))))))
let (flush_typ_or_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      typ_or_comp ->
        FStar_Tactics_Types.proofstate ->
          typ_or_comp FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun e ->
      fun tyc ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (367)) (Prims.of_int (4))
                                 (Prims.of_int (370)) (Prims.of_int (18))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (372)) (Prims.of_int (2))
                           (Prims.of_int (380)) (Prims.of_int (25)))))
          with
          | true ->
              (FStar_Tactics_Derived.try_with
                 (fun uu___ ->
                    match () with
                    | () ->
                        (match tyc with
                         | TC_Typ (ty, pl, n) ->
                             (fun ps1 ->
                                match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (374))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (374))
                                                       (Prims.of_int (37))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (367))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (370))
                                                 (Prims.of_int (18)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (37))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (367))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (370))
                                                                  (Prims.of_int (18))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (367))
                                                            (Prims.of_int (17))
                                                            (Prims.of_int (367))
                                                            (Prims.of_int (38))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (367))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (367))
                                                      (Prims.of_int (14)))))
                                     with
                                     | true ->
                                         ((match FStar_List_Tot_Base.splitAt
                                                   n pl
                                           with
                                           | (pl', uu___1) ->
                                               (fun ps2 ->
                                                  match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (26))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (369))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (370))
                                                                   (Prims.of_int (18)))))
                                                  with
                                                  | true ->
                                                      (match (_flush_typ_or_comp_comp
                                                                dbg e
                                                                (FStar_List_Tot_Base.rev
                                                                   pl') []
                                                                (FStar_Reflection_Builtins.pack_comp
                                                                   (FStar_Reflection_Data.C_Total
                                                                    (ty, []))))
                                                               (FStar_Tactics_Types.incr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (50))))))
                                                       with
                                                       | FStar_Tactics_Result.Success
                                                           (a, ps') ->
                                                           (match FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18)))))
                                                            with
                                                            | true ->
                                                                FStar_Tactics_Result.Success
                                                                  ((TC_Comp
                                                                    (a, pl,
                                                                    Prims.int_zero)),
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18))))))))
                                                       | FStar_Tactics_Result.Failed
                                                           (e1, ps') ->
                                                           FStar_Tactics_Result.Failed
                                                             (e1, ps')))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (37))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (367))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (370))
                                                                   (Prims.of_int (18))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (367))
                                                             (Prims.of_int (17))
                                                             (Prims.of_int (367))
                                                             (Prims.of_int (38))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (367))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (367))
                                                       (Prims.of_int (14))))))))
                         | TC_Comp (c, pl, n) ->
                             (fun ps1 ->
                                match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (367))
                                                       (Prims.of_int (17))
                                                       (Prims.of_int (367))
                                                       (Prims.of_int (38))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (367))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (367))
                                                 (Prims.of_int (14)))))
                                with
                                | true ->
                                    ((match FStar_List_Tot_Base.splitAt n pl
                                      with
                                      | (pl', uu___1) ->
                                          (fun ps2 ->
                                             match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (26))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (369))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (370))
                                                              (Prims.of_int (18)))))
                                             with
                                             | true ->
                                                 (match (_flush_typ_or_comp_comp
                                                           dbg e
                                                           (FStar_List_Tot_Base.rev
                                                              pl') [] c)
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (26))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (50))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a, ps') ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18)))))
                                                       with
                                                       | true ->
                                                           FStar_Tactics_Result.Success
                                                             ((TC_Comp
                                                                 (a, pl,
                                                                   Prims.int_zero)),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (18))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e1, ps') ->
                                                      FStar_Tactics_Result.Failed
                                                        (e1, ps')))))
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (367))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (367))
                                                        (Prims.of_int (38))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (367))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (367))
                                                  (Prims.of_int (14)))))))))
                 (fun uu___ ->
                    match uu___ with
                    | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                        FStar_InteractiveHelpers_Base.mfail
                          (Prims.strcat "flush_typ_or_comp failed on: "
                             (Prims.strcat (typ_or_comp_to_string tyc)
                                (Prims.strcat ":\n" msg)))
                    | err -> FStar_Tactics_Effect.raise err))
                (FStar_Tactics_Types.decr_depth
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (367)) (Prims.of_int (4))
                                  (Prims.of_int (370)) (Prims.of_int (18))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (372)) (Prims.of_int (2))
                            (Prims.of_int (380)) (Prims.of_int (25))))))
let (safe_arg_typ_or_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          typ_or_comp FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun e ->
      fun hd ->
        fun ps ->
          match (FStar_InteractiveHelpers_Base.print_dbg dbg
                   (Prims.strcat "safe_arg_typ_or_comp: "
                      (FStar_Reflection_Builtins.term_to_string hd)))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (387)) (Prims.of_int (2))
                              (Prims.of_int (387)) (Prims.of_int (62))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (388)) (Prims.of_int (2))
                                (Prims.of_int (408)) (Prims.of_int (15)))))
               with
               | true ->
                   (match (safe_tc e hd)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (388))
                                              (Prims.of_int (2))
                                              (Prims.of_int (408))
                                              (Prims.of_int (15))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (388))
                                        (Prims.of_int (8))
                                        (Prims.of_int (388))
                                        (Prims.of_int (20))))))
                    with
                    | FStar_Tactics_Result.Success (a1, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (388))
                                          (Prims.of_int (2))
                                          (Prims.of_int (408))
                                          (Prims.of_int (15)))))
                         with
                         | true ->
                             ((match a1 with
                               | FStar_Pervasives_Native.None ->
                                   (fun s ->
                                      FStar_Tactics_Result.Success
                                        (FStar_Pervasives_Native.None, s))
                               | FStar_Pervasives_Native.Some ty ->
                                   (fun ps1 ->
                                      match (FStar_InteractiveHelpers_Base.print_dbg
                                               dbg
                                               (Prims.strcat "hd type: "
                                                  (FStar_Reflection_Builtins.term_to_string
                                                     ty)))
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (391))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (391))
                                                          (Prims.of_int (51))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (392))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (408))
                                                            (Prims.of_int (15)))))
                                           with
                                           | true ->
                                               (match match match (FStar_Tactics_Builtins.inspect
                                                                    ty)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (15))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a3, ps'3) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31)))))
                                                                 with
                                                                 | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Data.uu___is_Tv_Arrow
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31))))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e1, ps'3) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e1, ps'3)
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a3, ps'3) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (11)))))
                                                           with
                                                           | true ->
                                                               (if a3
                                                                then
                                                                  (fun ps2 ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "no need to unfold the type")
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (50))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (11)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (ty,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (11))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4))
                                                                else
                                                                  (fun ps2 ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "need to unfold the type")
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (47))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (unfold_until_arrow
                                                                    e ty)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (40))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "result of unfolding : "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a5)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (67))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'6) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (14)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (14))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'6) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'6)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'5)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4)))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (11)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e1, ps'3) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e1, ps'3)
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a3, ps'3) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'3
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (15)))))
                                                     with
                                                     | true ->
                                                         (match (FStar_Tactics_Builtins.inspect
                                                                   a3)
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (15))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (20))))))
                                                          with
                                                          | FStar_Tactics_Result.Success
                                                              (a4, ps'4) ->
                                                              (match 
                                                                 FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (15)))))
                                                               with
                                                               | true ->
                                                                   ((match a4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Arrow
                                                                    (b, c) ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    ((FStar_Reflection_Derived.type_of_binder
                                                                    b), [],
                                                                    Prims.int_zero))),
                                                                    s))
                                                                    | 
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (15)))))))
                                                          | FStar_Tactics_Result.Failed
                                                              (e1, ps'4) ->
                                                              FStar_Tactics_Result.Failed
                                                                (e1, ps'4)))
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
                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (388))
                                           (Prims.of_int (2))
                                           (Prims.of_int (408))
                                           (Prims.of_int (15)))))))
                    | FStar_Tactics_Result.Failed (e1, ps'1) ->
                        FStar_Tactics_Result.Failed (e1, ps'1)))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (convert_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag -> FStar_Tactics_Types.ctrl_flag) =
  fun flag ->
    match flag with
    | FStar_Tactics_Types.Continue -> FStar_Tactics_Types.Continue
    | FStar_Tactics_Types.Skip -> FStar_Tactics_Types.Continue
    | FStar_Tactics_Types.Abort -> FStar_Tactics_Types.Abort
type 'a explorer =
  'a ->
    FStar_InteractiveHelpers_Base.genv ->
      (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
        Prims.list ->
        typ_or_comp FStar_Pervasives_Native.option ->
          FStar_Reflection_Data.term_view ->
            FStar_Tactics_Types.proofstate ->
              ('a * FStar_Tactics_Types.ctrl_flag)
                FStar_Tactics_Result.__result
let bind_expl :
  'a .
    'a ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Result.__result)
        ->
        ('a ->
           FStar_Tactics_Types.proofstate ->
             ('a * FStar_Tactics_Types.ctrl_flag)
               FStar_Tactics_Result.__result)
          ->
          FStar_Tactics_Types.proofstate ->
            ('a * FStar_Tactics_Types.ctrl_flag)
              FStar_Tactics_Result.__result
  =
  fun x ->
    fun f1 ->
      fun f2 ->
        fun ps ->
          match (f1 x)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (439)) (Prims.of_int (18))
                              (Prims.of_int (439)) (Prims.of_int (22))))))
          with
          | FStar_Tactics_Result.Success (a1, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (439)) (Prims.of_int (2))
                                (Prims.of_int (442)) (Prims.of_int (34)))))
               with
               | true ->
                   ((match a1 with
                     | (x1, flag1) ->
                         if flag1 = FStar_Tactics_Types.Continue
                         then f2 x1
                         else
                           (fun s ->
                              FStar_Tactics_Result.Success
                                ((x1, (convert_ctrl_flag flag1)), s))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (439)) (Prims.of_int (2))
                                 (Prims.of_int (442)) (Prims.of_int (34)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let rec (explore_term :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              (FStar_InteractiveHelpers_Base.genv *
                FStar_Reflection_Data.term_view) Prims.list ->
                typ_or_comp FStar_Pervasives_Native.option ->
                  FStar_Reflection_Types.term ->
                    FStar_Tactics_Types.proofstate ->
                      (Obj.t * FStar_Tactics_Types.ctrl_flag)
                        FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ge0 ->
              fun pl0 ->
                fun c0 ->
                  fun t0 ->
                    fun ps ->
                      match match match match (FStar_InteractiveHelpers_Base.term_construct
                                                 t0)
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (85))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (471))
                                                                    (Prims.of_int (85))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (471))
                                                                  (Prims.of_int (39))
                                                                  (Prims.of_int (471))
                                                                  (Prims.of_int (84))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (471))
                                                            (Prims.of_int (39))
                                                            (Prims.of_int (471))
                                                            (Prims.of_int (56))))))
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a1, ps') ->
                                            (match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (603))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (603))
                                                              (Prims.of_int (31)))))
                                             with
                                             | true ->
                                                 FStar_Tactics_Result.Success
                                                   ((Prims.strcat a1
                                                       (Prims.strcat ":\n"
                                                          (FStar_Reflection_Builtins.term_to_string
                                                             t0))),
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "prims.fst"
                                                                 (Prims.of_int (603))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (603))
                                                                 (Prims.of_int (31))))))))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps') ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps')
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps') ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (603))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (603))
                                                        (Prims.of_int (31)))))
                                       with
                                       | true ->
                                           FStar_Tactics_Result.Success
                                             ((Prims.strcat
                                                 "[> explore_term: " a1),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (603))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (603))
                                                           (Prims.of_int (31))))))))
                                  | FStar_Tactics_Result.Failed (e, ps') ->
                                      FStar_Tactics_Result.Failed (e, ps')
                            with
                            | FStar_Tactics_Result.Success (a1, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (471))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (471))
                                                  (Prims.of_int (85)))))
                                 with
                                 | true ->
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg a1)
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (85)))))))
                            | FStar_Tactics_Result.Failed (e, ps') ->
                                FStar_Tactics_Result.Failed (e, ps')
                      with
                      | FStar_Tactics_Result.Success (a1, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (472))
                                            (Prims.of_int (2))
                                            (Prims.of_int (551))
                                            (Prims.of_int (33)))))
                           with
                           | true ->
                               (match (FStar_Tactics_Builtins.inspect t0)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (472))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (551))
                                                          (Prims.of_int (33))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (472))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (472))
                                                    (Prims.of_int (22))))))
                                with
                                | FStar_Tactics_Result.Success (a2, ps'1) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (473))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (551))
                                                      (Prims.of_int (33)))))
                                     with
                                     | true ->
                                         (match (f x ge0 pl0 c0 a2)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (33))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (473))
                                                              (Prims.of_int (17))
                                                              (Prims.of_int (473))
                                                              (Prims.of_int (35))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a3, ps'2) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (473))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (551))
                                                                (Prims.of_int (33)))))
                                               with
                                               | true ->
                                                   ((match a3 with
                                                     | (x0, flag) ->
                                                         (fun ps1 ->
                                                            match FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (33)))))
                                                            with
                                                            | true ->
                                                                (if
                                                                   flag =
                                                                    FStar_Tactics_Types.Continue
                                                                 then
                                                                   (match a2
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_BVar
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (hd,
                                                                    (a4,
                                                                    qual)) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (safe_arg_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    hd)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (51))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Tv_App: updated target typ_or_comp to:\n"
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    typ_or_comp_to_string
                                                                    a5)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (64))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'4) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) a5
                                                                    a4)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (61))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a7
                                                                    with
                                                                    | (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    FStar_Pervasives_Native.None
                                                                    hd
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x1,
                                                                    (convert_ctrl_flag
                                                                    flag1)),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (38)))))))
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
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (br,
                                                                    body) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.genv_push_binder
                                                                    ge0 br
                                                                    false
                                                                    FStar_Pervasives_Native.None)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (50))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (47)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (abs_update_opt_typ_or_comp
                                                                    br c0
                                                                    a4.FStar_InteractiveHelpers_Base.env)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (47))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (55))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (47)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    a4
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) a5
                                                                    body)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (47)))))))
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
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Arrow
                                                                    (br, c01)
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Type
                                                                    () ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Refine
                                                                    (bv, ref)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    FStar_Pervasives_Native.None
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_sort)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (499))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv
                                                                    false
                                                                    FStar_Pervasives_Native.None)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (501))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (50)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    a5
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    FStar_Pervasives_Native.None
                                                                    ref)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (50)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x1,
                                                                    (convert_ctrl_flag
                                                                    flag1)),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (38)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Const
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Uvar
                                                                    (uu___,
                                                                    uu___1)
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Let
                                                                    (recf,
                                                                    attrs,
                                                                    bv, def,
                                                                    body) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))
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
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv
                                                                    false
                                                                    (FStar_Pervasives_Native.Some
                                                                    def))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (52))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))
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
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (67))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))
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
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (67))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (93))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match 
                                                                    if dfs
                                                                    then
                                                                    ((fun x1
                                                                    ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    a4
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) c0
                                                                    body),
                                                                    (fun x1
                                                                    ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    ((FStar_Reflection_Derived.type_of_bv
                                                                    bv), [],
                                                                    Prims.int_zero)))
                                                                    def))
                                                                    else
                                                                    (((
                                                                    fun x1 ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    ((FStar_Reflection_Derived.type_of_bv
                                                                    bv), [],
                                                                    Prims.int_zero)))
                                                                    def)),
                                                                    ((fun x1
                                                                    ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    a4
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) c0
                                                                    body)))
                                                                    with
                                                                    | (expl1,
                                                                    expl2) ->
                                                                    bind_expl
                                                                    x0 expl1
                                                                    expl2))
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
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (67))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (93))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (30)))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Match
                                                                    (scrutinee,
                                                                    _ret_opt,
                                                                    branches)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (safe_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    scrutinee)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (534))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) a4
                                                                    scrutinee)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (69))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    x_flag ->
                                                                    fun br ->
                                                                    fun ps3
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match x_flag
                                                                    with
                                                                    | (x01,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match br
                                                                    with
                                                                    | (pat,
                                                                    branch_body)
                                                                    ->
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (explore_pattern
                                                                    dbg dfs
                                                                    () f x01
                                                                    ge0 pat)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (70))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a6
                                                                    with
                                                                    | (ge1,
                                                                    x1,
                                                                    flag11)
                                                                    ->
                                                                    if
                                                                    flag11 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0) c0
                                                                    branch_body
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x1,
                                                                    (convert_ctrl_flag
                                                                    flag11)),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (28)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (30)))))))
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x01,
                                                                    flag1),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (20)))))))
                                                                    a5
                                                                    branches)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (42)))))))
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
                                                                    FStar_Reflection_Data.Tv_AscribedT
                                                                    (e, ty,
                                                                    tac) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (37)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    FStar_Pervasives_Native.None
                                                                    ty)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (37))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (65))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (37)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    (ty, [],
                                                                    Prims.int_zero)))
                                                                    e
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x1,
                                                                    (convert_ctrl_flag
                                                                    flag1)),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (37)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_AscribedC
                                                                    (e, c1,
                                                                    tac) ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0
                                                                    ((ge0,
                                                                    a2) ::
                                                                    pl0)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (TC_Comp
                                                                    (c1, [],
                                                                    Prims.int_zero)))
                                                                    e
                                                                    | 
                                                                    uu___ ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    FStar_Tactics_Types.Continue),
                                                                    s)))
                                                                 else
                                                                   (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x0,
                                                                    (convert_ctrl_flag
                                                                    flag)),
                                                                    s)))
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (33)))))))))
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                 (Prims.of_int (473))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (551))
                                                                 (Prims.of_int (33)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'2) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'2)))
                                | FStar_Tactics_Result.Failed (e, ps'1) ->
                                    FStar_Tactics_Result.Failed (e, ps'1)))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')
and (explore_pattern :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              FStar_Reflection_Data.pattern ->
                FStar_Tactics_Types.proofstate ->
                  (FStar_InteractiveHelpers_Base.genv * Obj.t *
                    FStar_Tactics_Types.ctrl_flag)
                    FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ge0 ->
              fun pat ->
                fun ps ->
                  match (FStar_InteractiveHelpers_Base.print_dbg dbg
                           "[> explore_pattern:")
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (554)) (Prims.of_int (2))
                                      (Prims.of_int (554))
                                      (Prims.of_int (39))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (555))
                                        (Prims.of_int (2))
                                        (Prims.of_int (574))
                                        (Prims.of_int (20)))))
                       with
                       | true ->
                           ((match pat with
                             | FStar_Reflection_Data.Pat_Constant uu___ ->
                                 (fun s ->
                                    FStar_Tactics_Result.Success
                                      ((ge0, x, FStar_Tactics_Types.Continue),
                                        s))
                             | FStar_Reflection_Data.Pat_Cons (fv, patterns)
                                 ->
                                 (fun ps1 ->
                                    match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (559))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (565))
                                                           (Prims.of_int (20))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (53)))))
                                    with
                                    | true ->
                                        (FStar_Tactics_Util.fold_left
                                           (fun ge_x_flag ->
                                              fun pat1 ->
                                                fun ps2 ->
                                                  match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (34))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (559))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (559))
                                                                   (Prims.of_int (22)))))
                                                  with
                                                  | true ->
                                                      ((match ge_x_flag with
                                                        | (ge01, x1, flag) ->
                                                            (fun ps3 ->
                                                               match 
                                                                 FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (17)))))
                                                               with
                                                               | true ->
                                                                   ((match pat1
                                                                    with
                                                                    | 
                                                                    (pat11,
                                                                    uu___) ->
                                                                    if
                                                                    flag =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    explore_pattern
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge01
                                                                    pat11
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge01,
                                                                    x1, flag),
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (17)))))))))
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (34))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (22)))))))
                                           (ge0, x,
                                             FStar_Tactics_Types.Continue)
                                           patterns)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (559))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (565))
                                                            (Prims.of_int (20))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (567))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (567))
                                                      (Prims.of_int (53)))))))
                             | FStar_Reflection_Data.Pat_Var bv ->
                                 (fun ps1 ->
                                    match (FStar_InteractiveHelpers_Base.genv_push_bv
                                             ge0 bv false
                                             FStar_Pervasives_Native.None)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (569))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (569))
                                                        (Prims.of_int (44))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (570))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (570))
                                                          (Prims.of_int (20)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((a2, x,
                                                  FStar_Tactics_Types.Continue),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (570))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (570))
                                                             (Prims.of_int (20))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1))
                             | FStar_Reflection_Data.Pat_Wild bv ->
                                 (fun ps1 ->
                                    match (FStar_InteractiveHelpers_Base.genv_push_bv
                                             ge0 bv false
                                             FStar_Pervasives_Native.None)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (569))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (569))
                                                        (Prims.of_int (44))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (570))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (570))
                                                          (Prims.of_int (20)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((a2, x,
                                                  FStar_Tactics_Types.Continue),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (570))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (570))
                                                             (Prims.of_int (20))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1))
                             | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
                                 (fun ps1 ->
                                    match (FStar_InteractiveHelpers_Base.genv_push_bv
                                             ge0 bv false
                                             FStar_Pervasives_Native.None)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (573))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (573))
                                                        (Prims.of_int (44))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (574))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (574))
                                                          (Prims.of_int (20)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((a2, x,
                                                  FStar_Tactics_Types.Continue),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (574))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (574))
                                                             (Prims.of_int (20))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1))))
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (555))
                                         (Prims.of_int (2))
                                         (Prims.of_int (574))
                                         (Prims.of_int (20)))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')
let (free_in :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.bv Prims.list FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (581)) (Prims.of_int (4))
                             (Prims.of_int (581)) (Prims.of_int (35))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range
                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                       (Prims.of_int (583)) (Prims.of_int (2))
                       (Prims.of_int (601)) (Prims.of_int (75)))))
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
                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (581))
                                              (Prims.of_int (4))
                                              (Prims.of_int (581))
                                              (Prims.of_int (35))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (583))
                                        (Prims.of_int (2))
                                        (Prims.of_int (601))
                                        (Prims.of_int (75))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (586)) (Prims.of_int (4))
                                  (Prims.of_int (597)) (Prims.of_int (23))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (599)) (Prims.of_int (2))
                            (Prims.of_int (601)) (Prims.of_int (75)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.top_env ())
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
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (581))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (581))
                                                            (Prims.of_int (35))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (583))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (601))
                                                      (Prims.of_int (75))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (586))
                                                (Prims.of_int (4))
                                                (Prims.of_int (597))
                                                (Prims.of_int (23))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (599))
                                          (Prims.of_int (2))
                                          (Prims.of_int (601))
                                          (Prims.of_int (75))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (599)) (Prims.of_int (10))
                                    (Prims.of_int (599)) (Prims.of_int (20))))))
                with
                | FStar_Tactics_Result.Success (a, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (600)) (Prims.of_int (2))
                                      (Prims.of_int (601))
                                      (Prims.of_int (75)))))
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
                                                       "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (600))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (601))
                                                       (Prims.of_int (75))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (600))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (600))
                                                 (Prims.of_int (26))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (601))
                                           (Prims.of_int (2))
                                           (Prims.of_int (601))
                                           (Prims.of_int (75)))))
                          with
                          | true ->
                              (match match Obj.magic
                                             ((explore_term false false ()
                                                 (Obj.magic
                                                    (fun fl ->
                                                       fun ge ->
                                                         fun pl ->
                                                           fun c ->
                                                             fun tv ->
                                                               fun s ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((match tv
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    bv ->
                                                                    (match 
                                                                    FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_ppname
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    ((if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    (FStar_List_Tot_Base.tryFind
                                                                    (fun bv2
                                                                    ->
                                                                    (FStar_Reflection_Derived.name_of_bv
                                                                    bv) =
                                                                    (FStar_Reflection_Derived.name_of_bv
                                                                    bv2)) fl)
                                                                    then fl
                                                                    else bv
                                                                    :: fl),
                                                                    FStar_Tactics_Types.Continue)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___ ->
                                                                    (fl,
                                                                    FStar_Tactics_Types.Continue))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_BVar
                                                                    bv ->
                                                                    (match 
                                                                    FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_ppname
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    ((if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    (FStar_List_Tot_Base.tryFind
                                                                    (fun bv2
                                                                    ->
                                                                    (FStar_Reflection_Derived.name_of_bv
                                                                    bv) =
                                                                    (FStar_Reflection_Derived.name_of_bv
                                                                    bv2)) fl)
                                                                    then fl
                                                                    else bv
                                                                    :: fl),
                                                                    FStar_Tactics_Types.Continue)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___ ->
                                                                    (fl,
                                                                    FStar_Tactics_Types.Continue))
                                                                    | 
                                                                    uu___ ->
                                                                    (fl,
                                                                    FStar_Tactics_Types.Continue)),
                                                                    s)))
                                                 (Obj.magic [])
                                                 (FStar_InteractiveHelpers_Base.mk_genv
                                                    a [] []) []
                                                 FStar_Pervasives_Native.None
                                                 t)
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (75))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (26))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (75))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (601))
                                                                  (Prims.of_int (15))
                                                                  (Prims.of_int (601))
                                                                  (Prims.of_int (75))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (601))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (601))
                                                            (Prims.of_int (74)))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (601))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (601))
                                                           (Prims.of_int (75)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Pervasives_Native.fst
                                                    a1),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (601))
                                                              (Prims.of_int (15))
                                                              (Prims.of_int (601))
                                                              (Prims.of_int (75))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)
                               with
                               | FStar_Tactics_Result.Success (a1, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (601))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (601))
                                                     (Prims.of_int (75)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((FStar_List_Tot_Base.rev a1),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (75))))))))
                               | FStar_Tactics_Result.Failed (e, ps'1) ->
                                   FStar_Tactics_Result.Failed (e, ps'1))))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
let (abs_free_in :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.bv Prims.list FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun t ->
      fun ps ->
        match (free_in t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (607)) (Prims.of_int (12))
                            (Prims.of_int (607)) (Prims.of_int (21))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (608)) (Prims.of_int (2))
                              (Prims.of_int (613)) (Prims.of_int (9)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((FStar_List_Tot_Base.filter
                       (fun bv ->
                          FStar_Pervasives_Native.uu___is_Some
                            (FStar_List_Tot_Base.find
                               (FStar_InteractiveHelpers_Base.bv_eq bv) a))
                       (FStar_List_Tot_Base.rev
                          (FStar_InteractiveHelpers_Base.genv_abstract_bvs ge))),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (608)) (Prims.of_int (2))
                                 (Prims.of_int (613)) (Prims.of_int (9))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (shadowed_free_in :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.bv Prims.list FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun t ->
      fun ps ->
        match (free_in t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (618)) (Prims.of_int (12))
                            (Prims.of_int (618)) (Prims.of_int (21))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (619)) (Prims.of_int (2))
                              (Prims.of_int (619)) (Prims.of_int (54)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((FStar_List_Tot_Base.filter
                       (fun bv ->
                          FStar_InteractiveHelpers_Base.bv_is_shadowed ge bv)
                       a),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (619)) (Prims.of_int (2))
                                 (Prims.of_int (619)) (Prims.of_int (54))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (term_has_shadowed_variables :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun t ->
      fun ps ->
        match (free_in t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (624)) (Prims.of_int (12))
                            (Prims.of_int (624)) (Prims.of_int (21))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (625)) (Prims.of_int (2))
                              (Prims.of_int (625)) (Prims.of_int (50)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((FStar_Pervasives_Native.uu___is_Some
                       (FStar_List_Tot_Base.tryFind
                          (FStar_InteractiveHelpers_Base.bv_is_shadowed ge) a)),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (625)) (Prims.of_int (2))
                                 (Prims.of_int (625)) (Prims.of_int (50))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')