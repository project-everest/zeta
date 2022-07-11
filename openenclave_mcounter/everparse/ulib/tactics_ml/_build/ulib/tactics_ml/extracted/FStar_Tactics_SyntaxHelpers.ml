open Prims
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      FStar_Tactics_Types.proofstate ->
        (FStar_Reflection_Types.binder Prims.list *
          FStar_Reflection_Types.comp) FStar_Tactics_Result.__result)
  =
  fun bs ->
    fun c ->
      match FStar_Reflection_Builtins.inspect_comp c with
      | FStar_Reflection_Data.C_Total (t, uu___) ->
          (fun ps ->
             match (FStar_Tactics_Builtins.inspect t)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (14)) (Prims.of_int (20))
                                 (Prims.of_int (14)) (Prims.of_int (29))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.SyntaxHelpers.fst"
                                   (Prims.of_int (14)) (Prims.of_int (14))
                                   (Prims.of_int (18)) (Prims.of_int (19)))))
                  with
                  | true ->
                      ((match a with
                        | FStar_Reflection_Data.Tv_Arrow (b, c1) ->
                            collect_arr' (b :: bs) c1
                        | uu___1 ->
                            (fun s ->
                               FStar_Tactics_Result.Success ((bs, c), s))))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.SyntaxHelpers.fst"
                                    (Prims.of_int (14)) (Prims.of_int (14))
                                    (Prims.of_int (18)) (Prims.of_int (19)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | uu___ -> (fun s -> FStar_Tactics_Result.Success ((bs, c), s))
let (collect_arr_bs :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.comp) FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (collect_arr' []
               (FStar_Reflection_Builtins.pack_comp
                  (FStar_Reflection_Data.C_Total (t, []))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (25)) (Prims.of_int (18))
                          (Prims.of_int (25)) (Prims.of_int (60))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                            (Prims.of_int (25)) (Prims.of_int (4))
                            (Prims.of_int (26)) (Prims.of_int (29)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (25)) (Prims.of_int (4))
                               (Prims.of_int (26)) (Prims.of_int (29))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (collect_arr :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp)
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (collect_arr' []
               (FStar_Reflection_Builtins.pack_comp
                  (FStar_Reflection_Data.C_Total (t, []))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (30)) (Prims.of_int (18))
                          (Prims.of_int (30)) (Prims.of_int (60))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                            (Prims.of_int (30)) (Prims.of_int (4))
                            (Prims.of_int (32)) (Prims.of_int (29)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs, c) ->
                        ((FStar_List_Tot_Base.rev
                            (FStar_List_Tot_Base.map
                               FStar_Reflection_Derived.type_of_binder bs)),
                          c))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (30)) (Prims.of_int (4))
                               (Prims.of_int (32)) (Prims.of_int (29))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        (FStar_Reflection_Types.binder Prims.list *
          FStar_Reflection_Types.term) FStar_Tactics_Result.__result)
  =
  fun bs ->
    fun t ->
      fun ps ->
        match (FStar_Tactics_Builtins.inspect t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                            (Prims.of_int (36)) (Prims.of_int (10))
                            (Prims.of_int (36)) (Prims.of_int (19))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                              (Prims.of_int (36)) (Prims.of_int (4))
                              (Prims.of_int (39)) (Prims.of_int (18)))))
             with
             | true ->
                 ((match a with
                   | FStar_Reflection_Data.Tv_Abs (b, t') ->
                       collect_abs' (b :: bs) t'
                   | uu___ ->
                       (fun s -> FStar_Tactics_Result.Success ((bs, t), s))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (36)) (Prims.of_int (4))
                               (Prims.of_int (39)) (Prims.of_int (18)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (collect_abs :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term) FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (collect_abs' [] t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (43)) (Prims.of_int (19))
                          (Prims.of_int (43)) (Prims.of_int (36))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                            (Prims.of_int (43)) (Prims.of_int (4))
                            (Prims.of_int (44)) (Prims.of_int (30)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t'))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (43)) (Prims.of_int (4))
                               (Prims.of_int (44)) (Prims.of_int (30))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let fail :
  'a .
    Prims.string ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun m -> FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m)
let rec (mk_arr :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStar_Tactics_Builtins.pack
            (FStar_Reflection_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          (fun ps ->
             match match match match (mk_arr bs1 cod)
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
                                                                    "FStar.Tactics.SyntaxHelpers.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (75))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.SyntaxHelpers.fst"
                                                               (Prims.of_int (54))
                                                               (Prims.of_int (34))
                                                               (Prims.of_int (54))
                                                               (Prims.of_int (74))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.SyntaxHelpers.fst"
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (45))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (73))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.SyntaxHelpers.fst"
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (69))))))
                               with
                               | FStar_Tactics_Result.Success (a, ps') ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.SyntaxHelpers.fst"
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (73)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((FStar_Reflection_Data.C_Total
                                              (a, [])),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.SyntaxHelpers.fst"
                                                        (Prims.of_int (54))
                                                        (Prims.of_int (45))
                                                        (Prims.of_int (54))
                                                        (Prims.of_int (73))))))))
                               | FStar_Tactics_Result.Failed (e, ps') ->
                                   FStar_Tactics_Result.Failed (e, ps')
                         with
                         | FStar_Tactics_Result.Success (a, ps') ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.SyntaxHelpers.fst"
                                               (Prims.of_int (54))
                                               (Prims.of_int (34))
                                               (Prims.of_int (54))
                                               (Prims.of_int (74)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    ((FStar_Reflection_Builtins.pack_comp a),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.SyntaxHelpers.fst"
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (74))))))))
                         | FStar_Tactics_Result.Failed (e, ps') ->
                             FStar_Tactics_Result.Failed (e, ps')
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.SyntaxHelpers.fst"
                                         (Prims.of_int (54))
                                         (Prims.of_int (22))
                                         (Prims.of_int (54))
                                         (Prims.of_int (75)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Data.Tv_Arrow (b, a)),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.SyntaxHelpers.fst"
                                            (Prims.of_int (54))
                                            (Prims.of_int (22))
                                            (Prims.of_int (54))
                                            (Prims.of_int (75))))))))
                   | FStar_Tactics_Result.Failed (e, ps') ->
                       FStar_Tactics_Result.Failed (e, ps')
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.SyntaxHelpers.fst"
                                   (Prims.of_int (54)) (Prims.of_int (17))
                                   (Prims.of_int (54)) (Prims.of_int (75)))))
                  with
                  | true ->
                      (FStar_Tactics_Builtins.pack a)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.SyntaxHelpers.fst"
                                    (Prims.of_int (54)) (Prims.of_int (17))
                                    (Prims.of_int (54)) (Prims.of_int (75)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec (mk_tot_arr :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> (fun s -> FStar_Tactics_Result.Success (cod, s))
      | b::bs1 ->
          (fun ps ->
             match match match match (mk_tot_arr bs1 cod)
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
                                                                    "FStar.Tactics.SyntaxHelpers.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (79))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.SyntaxHelpers.fst"
                                                               (Prims.of_int (59))
                                                               (Prims.of_int (34))
                                                               (Prims.of_int (59))
                                                               (Prims.of_int (78))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.SyntaxHelpers.fst"
                                                         (Prims.of_int (59))
                                                         (Prims.of_int (45))
                                                         (Prims.of_int (59))
                                                         (Prims.of_int (77))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.SyntaxHelpers.fst"
                                                   (Prims.of_int (59))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (59))
                                                   (Prims.of_int (73))))))
                               with
                               | FStar_Tactics_Result.Success (a, ps') ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.SyntaxHelpers.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (77)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((FStar_Reflection_Data.C_Total
                                              (a, [])),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.SyntaxHelpers.fst"
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (45))
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (77))))))))
                               | FStar_Tactics_Result.Failed (e, ps') ->
                                   FStar_Tactics_Result.Failed (e, ps')
                         with
                         | FStar_Tactics_Result.Success (a, ps') ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.SyntaxHelpers.fst"
                                               (Prims.of_int (59))
                                               (Prims.of_int (34))
                                               (Prims.of_int (59))
                                               (Prims.of_int (78)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    ((FStar_Reflection_Builtins.pack_comp a),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.SyntaxHelpers.fst"
                                                  (Prims.of_int (59))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (59))
                                                  (Prims.of_int (78))))))))
                         | FStar_Tactics_Result.Failed (e, ps') ->
                             FStar_Tactics_Result.Failed (e, ps')
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.SyntaxHelpers.fst"
                                         (Prims.of_int (59))
                                         (Prims.of_int (22))
                                         (Prims.of_int (59))
                                         (Prims.of_int (79)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Data.Tv_Arrow (b, a)),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.SyntaxHelpers.fst"
                                            (Prims.of_int (59))
                                            (Prims.of_int (22))
                                            (Prims.of_int (59))
                                            (Prims.of_int (79))))))))
                   | FStar_Tactics_Result.Failed (e, ps') ->
                       FStar_Tactics_Result.Failed (e, ps')
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.SyntaxHelpers.fst"
                                   (Prims.of_int (59)) (Prims.of_int (17))
                                   (Prims.of_int (59)) (Prims.of_int (79)))))
                  with
                  | true ->
                      (FStar_Tactics_Builtins.pack a)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.SyntaxHelpers.fst"
                                    (Prims.of_int (59)) (Prims.of_int (17))
                                    (Prims.of_int (59)) (Prims.of_int (79)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (lookup_lb_view :
  FStar_Reflection_Types.letbinding Prims.list ->
    FStar_Reflection_Types.name ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Data.lb_view FStar_Tactics_Result.__result)
  =
  fun lbs ->
    fun nm ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (62)) (Prims.of_int (10))
                               (Prims.of_int (66)) (Prims.of_int (16))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                         (Prims.of_int (68)) (Prims.of_int (2))
                         (Prims.of_int (70)) (Prims.of_int (56)))))
        with
        | true ->
            ((match FStar_List_Tot_Base.find
                      (fun lb ->
                         (FStar_Reflection_Builtins.inspect_fv
                            (FStar_Reflection_Builtins.inspect_lb lb).FStar_Reflection_Data.lb_fv)
                           = nm) lbs
              with
              | FStar_Pervasives_Native.Some lb ->
                  (fun s ->
                     FStar_Tactics_Result.Success
                       ((FStar_Reflection_Builtins.inspect_lb lb), s))
              | FStar_Pervasives_Native.None ->
                  fail "lookup_lb_view: Name not in let group"))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.SyntaxHelpers.fst"
                                (Prims.of_int (62)) (Prims.of_int (10))
                                (Prims.of_int (66)) (Prims.of_int (16))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (68)) (Prims.of_int (2))
                          (Prims.of_int (70)) (Prims.of_int (56))))))