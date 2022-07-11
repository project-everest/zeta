open Prims
type proposition = FStar_Reflection_Types.term
let (proposition_to_string : proposition -> Prims.string) =
  fun p -> FStar_Reflection_Builtins.term_to_string p
type assertions =
  {
  pres: proposition Prims.list ;
  posts: proposition Prims.list }
let (__proj__Mkassertions__item__pres : assertions -> proposition Prims.list)
  = fun projectee -> match projectee with | { pres; posts;_} -> pres
let (__proj__Mkassertions__item__posts :
  assertions -> proposition Prims.list) =
  fun projectee -> match projectee with | { pres; posts;_} -> posts
let (mk_assertions :
  proposition Prims.list -> proposition Prims.list -> assertions) =
  fun pres -> fun posts -> { pres; posts }
let (simpl_norm_steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.simplify;
  FStar_Pervasives.iota]
let (is_trivial_proposition :
  proposition ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun p ->
    fun s ->
      FStar_Tactics_Result.Success
        ((FStar_Reflection_Builtins.term_eq
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv ["Prims"; "l_True"]))) p),
          s)
let (simp_filter_proposition :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition ->
        FStar_Tactics_Types.proofstate ->
          proposition Prims.list FStar_Tactics_Result.__result)
  =
  fun e ->
    fun steps ->
      fun p ->
        fun ps ->
          match (FStar_Tactics_Builtins.norm_term_env e steps p)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Propositions.fst"
                              (Prims.of_int (50)) (Prims.of_int (14))
                              (Prims.of_int (50)) (Prims.of_int (37))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                (Prims.of_int (52)) (Prims.of_int (2))
                                (Prims.of_int (53)) (Prims.of_int (14)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     ((if
                         FStar_Reflection_Builtins.term_eq
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["Prims"; "l_True"]))) a
                       then []
                       else [a]),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                   (Prims.of_int (52)) (Prims.of_int (2))
                                   (Prims.of_int (53)) (Prims.of_int (14))))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (simp_filter_propositions :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition Prims.list ->
        FStar_Tactics_Types.proofstate ->
          proposition Prims.list FStar_Tactics_Result.__result)
  =
  fun e ->
    fun steps ->
      fun pl ->
        fun ps ->
          match (FStar_Tactics_Util.map (simp_filter_proposition e steps) pl)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Propositions.fst"
                              (Prims.of_int (57)) (Prims.of_int (15))
                              (Prims.of_int (57)) (Prims.of_int (57))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                (Prims.of_int (57)) (Prims.of_int (2))
                                (Prims.of_int (57)) (Prims.of_int (57)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     ((FStar_List_Tot_Base.flatten a),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                   (Prims.of_int (57)) (Prims.of_int (2))
                                   (Prims.of_int (57)) (Prims.of_int (57))))))))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')
let (simp_filter_assertions :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      assertions ->
        FStar_Tactics_Types.proofstate ->
          assertions FStar_Tactics_Result.__result)
  =
  fun e ->
    fun steps ->
      fun a ->
        fun ps ->
          match (simp_filter_propositions e steps a.pres)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Propositions.fst"
                              (Prims.of_int (61)) (Prims.of_int (13))
                              (Prims.of_int (61)) (Prims.of_int (52))))))
          with
          | FStar_Tactics_Result.Success (a1, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                (Prims.of_int (62)) (Prims.of_int (2))
                                (Prims.of_int (63)) (Prims.of_int (26)))))
               with
               | true ->
                   (match (simp_filter_propositions e steps a.posts)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                              (Prims.of_int (62))
                                              (Prims.of_int (2))
                                              (Prims.of_int (63))
                                              (Prims.of_int (26))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                        (Prims.of_int (62))
                                        (Prims.of_int (14))
                                        (Prims.of_int (62))
                                        (Prims.of_int (54))))))
                    with
                    | FStar_Tactics_Result.Success (a2, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                          (Prims.of_int (63))
                                          (Prims.of_int (2))
                                          (Prims.of_int (63))
                                          (Prims.of_int (26)))))
                         with
                         | true ->
                             FStar_Tactics_Result.Success
                               ((mk_assertions a1 a2),
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Propositions.fst"
                                             (Prims.of_int (63))
                                             (Prims.of_int (2))
                                             (Prims.of_int (63))
                                             (Prims.of_int (26))))))))
                    | FStar_Tactics_Result.Failed (e1, ps'1) ->
                        FStar_Tactics_Result.Failed (e1, ps'1)))
          | FStar_Tactics_Result.Failed (e1, ps') ->
              FStar_Tactics_Result.Failed (e1, ps')