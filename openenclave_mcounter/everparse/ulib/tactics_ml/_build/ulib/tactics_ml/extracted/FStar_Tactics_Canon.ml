open Prims



















let (step :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Canon"; "trans"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (126)) (Prims.of_int (4))
                          (Prims.of_int (126)) (Prims.of_int (24))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Canon.fst"
                            (Prims.of_int (127)) (Prims.of_int (4))
                            (Prims.of_int (127)) (Prims.of_int (8)))))
           with
           | true ->
               (t ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Canon.fst"
                             (Prims.of_int (127)) (Prims.of_int (4))
                             (Prims.of_int (127)) (Prims.of_int (8)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (step_lemma :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun lem -> step (fun uu___ -> FStar_Tactics_Derived.apply_lemma lem)
let rec (canon_point :
  FStar_Reflection_Arith.expr ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Arith.expr FStar_Tactics_Result.__result)
  =
  fun e ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Canon.fst"
                             (Prims.of_int (136)) (Prims.of_int (8))
                             (Prims.of_int (136)) (Prims.of_int (19))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                       (Prims.of_int (138)) (Prims.of_int (4))
                       (Prims.of_int (250)) (Prims.of_int (15)))))
      with
      | true ->
          ((match e with
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Lit a, FStar_Reflection_Arith.Lit b)
                ->
                (fun ps1 ->
                   match (FStar_Tactics_Builtins.norm
                            [FStar_Pervasives.primops])
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (141))
                                       (Prims.of_int (8))
                                       (Prims.of_int (141))
                                       (Prims.of_int (22))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (142))
                                         (Prims.of_int (8))
                                         (Prims.of_int (143))
                                         (Prims.of_int (19)))))
                        with
                        | true ->
                            (match (FStar_Tactics_Derived.trefl ())
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (142))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (143))
                                                       (Prims.of_int (19))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (142))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (142))
                                                 (Prims.of_int (16))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (143))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (143))
                                                   (Prims.of_int (19)))))
                                  with
                                  | true ->
                                      FStar_Tactics_Result.Success
                                        ((FStar_Reflection_Arith.Lit (a + b)),
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (143))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (143))
                                                      (Prims.of_int (19))))))))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit a, FStar_Reflection_Arith.Lit b)
                ->
                (fun ps1 ->
                   match (FStar_Tactics_Builtins.norm
                            [FStar_Pervasives.delta;
                            FStar_Pervasives.primops])
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (146))
                                       (Prims.of_int (8))
                                       (Prims.of_int (146))
                                       (Prims.of_int (29))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (147))
                                         (Prims.of_int (8))
                                         (Prims.of_int (148))
                                         (Prims.of_int (19)))))
                        with
                        | true ->
                            (match (FStar_Tactics_Derived.trefl ())
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (147))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (148))
                                                       (Prims.of_int (19))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (147))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (147))
                                                 (Prims.of_int (16))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (148))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (148))
                                                   (Prims.of_int (19)))))
                                  with
                                  | true ->
                                      FStar_Tactics_Result.Success
                                        ((FStar_Reflection_Arith.Lit (a * b)),
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (148))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (148))
                                                      (Prims.of_int (19))))))))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Neg e1 ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "neg_minus_one"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (152))
                                       (Prims.of_int (8))
                                       (Prims.of_int (152))
                                       (Prims.of_int (35))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (153))
                                         (Prims.of_int (8))
                                         (Prims.of_int (153))
                                         (Prims.of_int (39)))))
                        with
                        | true ->
                            (canon_point
                               (FStar_Reflection_Arith.Mult
                                  ((FStar_Reflection_Arith.Lit
                                      (Prims.of_int (-1))), e1)))
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Canon.fst"
                                          (Prims.of_int (153))
                                          (Prims.of_int (8))
                                          (Prims.of_int (153))
                                          (Prims.of_int (39)))))))
                   | FStar_Tactics_Result.Failed (e2, ps') ->
                       FStar_Tactics_Result.Failed (e2, ps'))
            | FStar_Reflection_Arith.Mult
                (a, FStar_Reflection_Arith.Plus (b, c)) ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Tactics"; "Canon"; "distr"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (157))
                                       (Prims.of_int (8))
                                       (Prims.of_int (157))
                                       (Prims.of_int (27))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (158))
                                         (Prims.of_int (8))
                                         (Prims.of_int (161))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (match (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"]))))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (158))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (161))
                                                       (Prims.of_int (30))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (158))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (158))
                                                 (Prims.of_int (31))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (159))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (161))
                                                   (Prims.of_int (30)))))
                                  with
                                  | true ->
                                      (match (canon_point
                                                (FStar_Reflection_Arith.Mult
                                                   (a, b)))
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (159))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (30))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (159))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (159))
                                                           (Prims.of_int (38))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a3, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (160))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (30)))))
                                            with
                                            | true ->
                                                (match (canon_point
                                                          (FStar_Reflection_Arith.Mult
                                                             (a, c)))
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (30))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (38))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (30)))))
                                                      with
                                                      | true ->
                                                          (canon_point
                                                             (FStar_Reflection_Arith.Plus
                                                                (a3, a4)))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e1, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e1, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e1, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e1, ps'2)))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Plus (a, b), c) ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar"; "Tactics"; "Canon"; "distl"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (164))
                                       (Prims.of_int (8))
                                       (Prims.of_int (164))
                                       (Prims.of_int (27))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (165))
                                         (Prims.of_int (8))
                                         (Prims.of_int (168))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (match (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"]))))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (168))
                                                       (Prims.of_int (30))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (31))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (166))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (168))
                                                   (Prims.of_int (30)))))
                                  with
                                  | true ->
                                      (match (canon_point
                                                (FStar_Reflection_Arith.Mult
                                                   (a, c)))
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (166))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (168))
                                                                 (Prims.of_int (30))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (166))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (166))
                                                           (Prims.of_int (38))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a3, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (167))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (168))
                                                             (Prims.of_int (30)))))
                                            with
                                            | true ->
                                                (match (canon_point
                                                          (FStar_Reflection_Arith.Mult
                                                             (b, c)))
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (30))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (38))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (30)))))
                                                      with
                                                      | true ->
                                                          (canon_point
                                                             (FStar_Reflection_Arith.Plus
                                                                (a3, a4)))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e1, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e1, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e1, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e1, ps'2)))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (a, FStar_Reflection_Arith.Mult (b, c)) ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "ass_mult_l"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (172))
                                       (Prims.of_int (8))
                                       (Prims.of_int (172))
                                       (Prims.of_int (32))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (173))
                                         (Prims.of_int (8))
                                         (Prims.of_int (176))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (match (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_mult"]))))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (173))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (176))
                                                       (Prims.of_int (30))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (173))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (173))
                                                 (Prims.of_int (31))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (174))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (176))
                                                   (Prims.of_int (30)))))
                                  with
                                  | true ->
                                      (match (canon_point
                                                (FStar_Reflection_Arith.Mult
                                                   (a, b)))
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (174))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (176))
                                                                 (Prims.of_int (30))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (174))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (174))
                                                           (Prims.of_int (38))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a3, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (175))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (176))
                                                             (Prims.of_int (30)))))
                                            with
                                            | true ->
                                                (match (canon_point c)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (30))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (29))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (30)))))
                                                      with
                                                      | true ->
                                                          (canon_point
                                                             (FStar_Reflection_Arith.Mult
                                                                (a3, a4)))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e1, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e1, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e1, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e1, ps'2)))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Plus
                (a, FStar_Reflection_Arith.Plus (b, c)) ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "ass_plus_l"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (179))
                                       (Prims.of_int (8))
                                       (Prims.of_int (179))
                                       (Prims.of_int (32))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (180))
                                         (Prims.of_int (8))
                                         (Prims.of_int (183))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (match (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"]))))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (180))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (183))
                                                       (Prims.of_int (30))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (180))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (180))
                                                 (Prims.of_int (31))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (183))
                                                   (Prims.of_int (30)))))
                                  with
                                  | true ->
                                      (match (canon_point
                                                (FStar_Reflection_Arith.Plus
                                                   (a, b)))
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (181))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (183))
                                                                 (Prims.of_int (30))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (181))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (181))
                                                           (Prims.of_int (38))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a3, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (182))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (183))
                                                             (Prims.of_int (30)))))
                                            with
                                            | true ->
                                                (match (canon_point c)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (30))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (29))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (30)))))
                                                      with
                                                      | true ->
                                                          (canon_point
                                                             (FStar_Reflection_Arith.Plus
                                                                (a3, a4)))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e1, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e1, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e1, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e1, ps'2)))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Plus (a, b), c) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr b c)
                then
                  (fun ps1 ->
                     match (step_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "Canon";
                                       "sw_plus"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (188))
                                         (Prims.of_int (12))
                                         (Prims.of_int (188))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (189))
                                           (Prims.of_int (12))
                                           (Prims.of_int (192))
                                           (Prims.of_int (20)))))
                          with
                          | true ->
                              (match (FStar_Tactics_Derived.apply_lemma
                                        (FStar_Reflection_Builtins.pack_ln
                                           (FStar_Reflection_Data.Tv_FVar
                                              (FStar_Reflection_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "cong_plus"]))))
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (189))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (192))
                                                         (Prims.of_int (20))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (189))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (189))
                                                   (Prims.of_int (36))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Canon.fst"
                                                     (Prims.of_int (190))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (192))
                                                     (Prims.of_int (20)))))
                                    with
                                    | true ->
                                        (match (canon_point
                                                  (FStar_Reflection_Arith.Plus
                                                     (a, c)))
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Canon.fst"
                                                                   (Prims.of_int (190))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (192))
                                                                   (Prims.of_int (20))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (190))
                                                             (Prims.of_int (20))
                                                             (Prims.of_int (190))
                                                             (Prims.of_int (42))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a3, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (191))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (192))
                                                               (Prims.of_int (20)))))
                                              with
                                              | true ->
                                                  (match (FStar_Tactics_Derived.trefl
                                                            ())
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (19))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a4, ps'3) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'3
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20)))))
                                                        with
                                                        | true ->
                                                            FStar_Tactics_Result.Success
                                                              ((FStar_Reflection_Arith.Plus
                                                                  (a3, b)),
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))))))))
                                                   | FStar_Tactics_Result.Failed
                                                       (e1, ps'3) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e1, ps'3)))
                                         | FStar_Tactics_Result.Failed
                                             (e1, ps'2) ->
                                             FStar_Tactics_Result.Failed
                                               (e1, ps'2)))
                               | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                   FStar_Tactics_Result.Failed (e1, ps'1)))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.trefl ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (136))
                                         (Prims.of_int (8))
                                         (Prims.of_int (136))
                                         (Prims.of_int (16))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (134))
                                           (Prims.of_int (28))
                                           (Prims.of_int (134))
                                           (Prims.of_int (29)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (e,
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (134))
                                              (Prims.of_int (28))
                                              (Prims.of_int (134))
                                              (Prims.of_int (29))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Mult (a, b), c) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr b c)
                then
                  (fun ps1 ->
                     match (step_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "Canon";
                                       "sw_mult"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (199))
                                         (Prims.of_int (12))
                                         (Prims.of_int (199))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (200))
                                           (Prims.of_int (12))
                                           (Prims.of_int (203))
                                           (Prims.of_int (20)))))
                          with
                          | true ->
                              (match (FStar_Tactics_Derived.apply_lemma
                                        (FStar_Reflection_Builtins.pack_ln
                                           (FStar_Reflection_Data.Tv_FVar
                                              (FStar_Reflection_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "cong_mult"]))))
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (200))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (203))
                                                         (Prims.of_int (20))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (200))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (200))
                                                   (Prims.of_int (36))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Canon.fst"
                                                     (Prims.of_int (201))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (203))
                                                     (Prims.of_int (20)))))
                                    with
                                    | true ->
                                        (match (canon_point
                                                  (FStar_Reflection_Arith.Mult
                                                     (a, c)))
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Canon.fst"
                                                                   (Prims.of_int (201))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (203))
                                                                   (Prims.of_int (20))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (201))
                                                             (Prims.of_int (20))
                                                             (Prims.of_int (201))
                                                             (Prims.of_int (42))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a3, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (202))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (203))
                                                               (Prims.of_int (20)))))
                                              with
                                              | true ->
                                                  (match (FStar_Tactics_Derived.trefl
                                                            ())
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (20))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a4, ps'3) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'3
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20)))))
                                                        with
                                                        | true ->
                                                            FStar_Tactics_Result.Success
                                                              ((FStar_Reflection_Arith.Mult
                                                                  (a3, b)),
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (20))))))))
                                                   | FStar_Tactics_Result.Failed
                                                       (e1, ps'3) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e1, ps'3)))
                                         | FStar_Tactics_Result.Failed
                                             (e1, ps'2) ->
                                             FStar_Tactics_Result.Failed
                                               (e1, ps'2)))
                               | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                   FStar_Tactics_Result.Failed (e1, ps'1)))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.trefl ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (136))
                                         (Prims.of_int (8))
                                         (Prims.of_int (136))
                                         (Prims.of_int (16))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (134))
                                           (Prims.of_int (28))
                                           (Prims.of_int (134))
                                           (Prims.of_int (29)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (e,
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (134))
                                              (Prims.of_int (28))
                                              (Prims.of_int (134))
                                              (Prims.of_int (29))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Plus
                (a, FStar_Reflection_Arith.Lit uu___) when
                uu___ = Prims.int_zero ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "x_plus_zero"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (208))
                                       (Prims.of_int (8))
                                       (Prims.of_int (208))
                                       (Prims.of_int (34))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (207))
                                         (Prims.of_int (11))
                                         (Prims.of_int (207))
                                         (Prims.of_int (12)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              (a,
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (207))
                                            (Prims.of_int (11))
                                            (Prims.of_int (207))
                                            (Prims.of_int (12))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Lit uu___, b) when
                uu___ = Prims.int_zero ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "zero_plus_x"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (212))
                                       (Prims.of_int (8))
                                       (Prims.of_int (212))
                                       (Prims.of_int (34))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (211))
                                         (Prims.of_int (19))
                                         (Prims.of_int (211))
                                         (Prims.of_int (20)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              (b,
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (211))
                                            (Prims.of_int (19))
                                            (Prims.of_int (211))
                                            (Prims.of_int (20))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Plus (a, b) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr a b)
                then
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "Canon";
                                       "comm_plus"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (217))
                                         (Prims.of_int (14))
                                         (Prims.of_int (217))
                                         (Prims.of_int (38))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (217))
                                           (Prims.of_int (40))
                                           (Prims.of_int (217))
                                           (Prims.of_int (48)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Arith.Plus (b, a)),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (217))
                                              (Prims.of_int (40))
                                              (Prims.of_int (217))
                                              (Prims.of_int (48))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.trefl ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (136))
                                         (Prims.of_int (8))
                                         (Prims.of_int (136))
                                         (Prims.of_int (16))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (134))
                                           (Prims.of_int (28))
                                           (Prims.of_int (134))
                                           (Prims.of_int (29)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (e,
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (134))
                                              (Prims.of_int (28))
                                              (Prims.of_int (134))
                                              (Prims.of_int (29))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit uu___, uu___1) when
                uu___ = Prims.int_zero ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "zero_mult_x"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (221))
                                       (Prims.of_int (8))
                                       (Prims.of_int (221))
                                       (Prims.of_int (34))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (222))
                                         (Prims.of_int (8))
                                         (Prims.of_int (222))
                                         (Prims.of_int (13)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Arith.Lit Prims.int_zero),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (222))
                                            (Prims.of_int (8))
                                            (Prims.of_int (222))
                                            (Prims.of_int (13))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (uu___, FStar_Reflection_Arith.Lit uu___1) when
                uu___1 = Prims.int_zero ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "x_mult_zero"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (225))
                                       (Prims.of_int (8))
                                       (Prims.of_int (225))
                                       (Prims.of_int (34))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (226))
                                         (Prims.of_int (8))
                                         (Prims.of_int (226))
                                         (Prims.of_int (13)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Arith.Lit Prims.int_zero),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (226))
                                            (Prims.of_int (8))
                                            (Prims.of_int (226))
                                            (Prims.of_int (13))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit uu___, r) when
                uu___ = Prims.int_one ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "one_mult_x"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (229))
                                       (Prims.of_int (8))
                                       (Prims.of_int (229))
                                       (Prims.of_int (33))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (228))
                                         (Prims.of_int (19))
                                         (Prims.of_int (228))
                                         (Prims.of_int (20)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              (r,
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (228))
                                            (Prims.of_int (19))
                                            (Prims.of_int (228))
                                            (Prims.of_int (20))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult
                (l, FStar_Reflection_Arith.Lit uu___) when
                uu___ = Prims.int_one ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.apply_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "x_mult_one"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (233))
                                       (Prims.of_int (8))
                                       (Prims.of_int (233))
                                       (Prims.of_int (33))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (232))
                                         (Prims.of_int (11))
                                         (Prims.of_int (232))
                                         (Prims.of_int (12)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              (l,
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (232))
                                            (Prims.of_int (11))
                                            (Prims.of_int (232))
                                            (Prims.of_int (12))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Mult (a, b) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr a b)
                then
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "Canon";
                                       "comm_mult"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (238))
                                         (Prims.of_int (14))
                                         (Prims.of_int (238))
                                         (Prims.of_int (38))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (238))
                                           (Prims.of_int (40))
                                           (Prims.of_int (238))
                                           (Prims.of_int (48)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Arith.Mult (b, a)),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (238))
                                              (Prims.of_int (40))
                                              (Prims.of_int (238))
                                              (Prims.of_int (48))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.trefl ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (136))
                                         (Prims.of_int (8))
                                         (Prims.of_int (136))
                                         (Prims.of_int (16))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (134))
                                           (Prims.of_int (28))
                                           (Prims.of_int (134))
                                           (Prims.of_int (29)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (e,
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (134))
                                              (Prims.of_int (28))
                                              (Prims.of_int (134))
                                              (Prims.of_int (29))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps'))
            | FStar_Reflection_Arith.Minus (a, b) ->
                (fun ps1 ->
                   match (step_lemma
                            (FStar_Reflection_Builtins.pack_ln
                               (FStar_Reflection_Data.Tv_FVar
                                  (FStar_Reflection_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Canon";
                                     "minus_is_plus"]))))
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (243))
                                       (Prims.of_int (8))
                                       (Prims.of_int (243))
                                       (Prims.of_int (35))))))
                   with
                   | FStar_Tactics_Result.Success (a1, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (244))
                                         (Prims.of_int (8))
                                         (Prims.of_int (247))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (match (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"]))))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Canon.fst"
                                                       (Prims.of_int (244))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (247))
                                                       (Prims.of_int (30))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (244))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (244))
                                                 (Prims.of_int (31))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (245))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (247))
                                                   (Prims.of_int (30)))))
                                  with
                                  | true ->
                                      (match (FStar_Tactics_Derived.trefl ())
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (245))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (247))
                                                                 (Prims.of_int (30))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (245))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (245))
                                                           (Prims.of_int (16))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a3, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (246))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (247))
                                                             (Prims.of_int (30)))))
                                            with
                                            | true ->
                                                (match (canon_point
                                                          (FStar_Reflection_Arith.Neg
                                                             b))
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (35))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a4, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))))
                                                      with
                                                      | true ->
                                                          (canon_point
                                                             (FStar_Reflection_Arith.Plus
                                                                (a, a4)))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e1, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e1, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e1, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e1, ps'2)))
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))
            | uu___ ->
                (fun ps1 ->
                   match (FStar_Tactics_Derived.trefl ())
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Canon.fst"
                                       (Prims.of_int (136))
                                       (Prims.of_int (8))
                                       (Prims.of_int (136))
                                       (Prims.of_int (16))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (134))
                                         (Prims.of_int (28))
                                         (Prims.of_int (134))
                                         (Prims.of_int (29)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              (e,
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Canon.fst"
                                            (Prims.of_int (134))
                                            (Prims.of_int (28))
                                            (Prims.of_int (134))
                                            (Prims.of_int (29))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (136)) (Prims.of_int (8))
                              (Prims.of_int (136)) (Prims.of_int (19))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (138)) (Prims.of_int (4))
                        (Prims.of_int (250)) (Prims.of_int (15))))))
let (canon_point_entry :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.norm [])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (264)) (Prims.of_int (4))
                          (Prims.of_int (264)) (Prims.of_int (11))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Canon.fst"
                            (Prims.of_int (265)) (Prims.of_int (4))
                            (Prims.of_int (273)) (Prims.of_int (48)))))
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
                                          "FStar.Tactics.Canon.fst"
                                          (Prims.of_int (265))
                                          (Prims.of_int (4))
                                          (Prims.of_int (273))
                                          (Prims.of_int (48))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Canon.fst"
                                    (Prims.of_int (265)) (Prims.of_int (12))
                                    (Prims.of_int (265)) (Prims.of_int (23))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Canon.fst"
                                      (Prims.of_int (266)) (Prims.of_int (4))
                                      (Prims.of_int (273))
                                      (Prims.of_int (48)))))
                     with
                     | true ->
                         (match (FStar_Reflection_Formula.term_as_formula a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (266))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (273))
                                                    (Prims.of_int (48))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (266))
                                              (Prims.of_int (10))
                                              (Prims.of_int (266))
                                              (Prims.of_int (27))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Canon.fst"
                                                (Prims.of_int (266))
                                                (Prims.of_int (4))
                                                (Prims.of_int (273))
                                                (Prims.of_int (48)))))
                               with
                               | true ->
                                   ((match a2 with
                                     | FStar_Reflection_Formula.Comp
                                         (FStar_Reflection_Formula.Eq uu___1,
                                          l, r)
                                         ->
                                         (fun ps1 ->
                                            match (FStar_Reflection_Arith.run_tm
                                                     (FStar_Reflection_Arith.is_arith_expr
                                                        l))
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Canon.fst"
                                                                (Prims.of_int (268))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (268))
                                                                (Prims.of_int (44))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Canon.fst"
                                                                  (Prims.of_int (268))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (270))
                                                                  (Prims.of_int (27)))))
                                                 with
                                                 | true ->
                                                     ((match a3 with
                                                       | FStar_Pervasives.Inr
                                                           e ->
                                                           (fun ps2 ->
                                                              match (canon_point
                                                                    e)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (42))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a4, ps'4)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (48)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (48))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e1, ps'4)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'4))
                                                       | FStar_Pervasives.Inl
                                                           uu___2 ->
                                                           FStar_Tactics_Derived.trefl
                                                             ()))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'3
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Canon.fst"
                                                                   (Prims.of_int (268))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (270))
                                                                   (Prims.of_int (27)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3))
                                     | uu___1 ->
                                         FStar_Tactics_Derived.fail
                                           (Prims.strcat "impossible: "
                                              (FStar_Reflection_Builtins.term_to_string
                                                 a1))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Canon.fst"
                                                 (Prims.of_int (266))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (273))
                                                 (Prims.of_int (48)))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (canon :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.pointwise canon_point_entry