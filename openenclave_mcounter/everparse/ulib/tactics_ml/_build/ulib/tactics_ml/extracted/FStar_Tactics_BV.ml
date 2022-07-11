open Prims















let rec (arith_expr_to_bv :
  FStar_Reflection_Arith.expr ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun e ->
    match e with
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.MulMod
        (e1, uu___)) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_mul"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (113)) (Prims.of_int (8))
                               (Prims.of_int (113)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (114)) (Prims.of_int (8))
                                 (Prims.of_int (115)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvmul"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (8))
                                               (Prims.of_int (115))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (114))
                                         (Prims.of_int (8))
                                         (Prims.of_int (114))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (115))
                                           (Prims.of_int (8))
                                           (Prims.of_int (115))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (115))
                                            (Prims.of_int (8))
                                            (Prims.of_int (115))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.MulMod (e1, uu___) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_mul"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (113)) (Prims.of_int (8))
                               (Prims.of_int (113)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (114)) (Prims.of_int (8))
                                 (Prims.of_int (115)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvmul"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (114))
                                               (Prims.of_int (8))
                                               (Prims.of_int (115))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (114))
                                         (Prims.of_int (8))
                                         (Prims.of_int (114))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (115))
                                           (Prims.of_int (8))
                                           (Prims.of_int (115))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (115))
                                            (Prims.of_int (8))
                                            (Prims.of_int (115))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Umod
        (e1, uu___)) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_mod"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (117)) (Prims.of_int (8))
                               (Prims.of_int (117)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (118)) (Prims.of_int (8))
                                 (Prims.of_int (119)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvmod"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (118))
                                               (Prims.of_int (8))
                                               (Prims.of_int (119))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (118))
                                         (Prims.of_int (8))
                                         (Prims.of_int (118))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (119))
                                           (Prims.of_int (8))
                                           (Prims.of_int (119))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (119))
                                            (Prims.of_int (8))
                                            (Prims.of_int (119))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.Umod (e1, uu___) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_mod"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (117)) (Prims.of_int (8))
                               (Prims.of_int (117)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (118)) (Prims.of_int (8))
                                 (Prims.of_int (119)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvmod"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (118))
                                               (Prims.of_int (8))
                                               (Prims.of_int (119))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (118))
                                         (Prims.of_int (8))
                                         (Prims.of_int (118))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (119))
                                           (Prims.of_int (8))
                                           (Prims.of_int (119))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (119))
                                            (Prims.of_int (8))
                                            (Prims.of_int (119))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Udiv
        (e1, uu___)) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_div"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (121)) (Prims.of_int (8))
                               (Prims.of_int (121)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (122)) (Prims.of_int (8))
                                 (Prims.of_int (123)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvdiv"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (122))
                                         (Prims.of_int (8))
                                         (Prims.of_int (122))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (123))
                                           (Prims.of_int (8))
                                           (Prims.of_int (123))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (123))
                                            (Prims.of_int (8))
                                            (Prims.of_int (123))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.Udiv (e1, uu___) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_div"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (121)) (Prims.of_int (8))
                               (Prims.of_int (121)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (122)) (Prims.of_int (8))
                                 (Prims.of_int (123)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvdiv"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (122))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (122))
                                         (Prims.of_int (8))
                                         (Prims.of_int (122))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (123))
                                           (Prims.of_int (8))
                                           (Prims.of_int (123))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (123))
                                            (Prims.of_int (8))
                                            (Prims.of_int (123))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Shl (e1, uu___))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_shl"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (125)) (Prims.of_int (8))
                               (Prims.of_int (125)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (126)) (Prims.of_int (8))
                                 (Prims.of_int (127)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvshl"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (126))
                                               (Prims.of_int (8))
                                               (Prims.of_int (127))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (126))
                                         (Prims.of_int (8))
                                         (Prims.of_int (126))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (127))
                                           (Prims.of_int (8))
                                           (Prims.of_int (127))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (127))
                                            (Prims.of_int (8))
                                            (Prims.of_int (127))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.Shl (e1, uu___) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_shl"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (125)) (Prims.of_int (8))
                               (Prims.of_int (125)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (126)) (Prims.of_int (8))
                                 (Prims.of_int (127)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvshl"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (126))
                                               (Prims.of_int (8))
                                               (Prims.of_int (127))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (126))
                                         (Prims.of_int (8))
                                         (Prims.of_int (126))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (127))
                                           (Prims.of_int (8))
                                           (Prims.of_int (127))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (127))
                                            (Prims.of_int (8))
                                            (Prims.of_int (127))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Shr (e1, uu___))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_shr"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (129)) (Prims.of_int (8))
                               (Prims.of_int (129)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (130)) (Prims.of_int (8))
                                 (Prims.of_int (131)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvshr"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (130))
                                               (Prims.of_int (8))
                                               (Prims.of_int (131))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (130))
                                         (Prims.of_int (8))
                                         (Prims.of_int (130))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (131))
                                           (Prims.of_int (8))
                                           (Prims.of_int (131))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (131))
                                            (Prims.of_int (8))
                                            (Prims.of_int (131))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.Shr (e1, uu___) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_shr"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (129)) (Prims.of_int (8))
                               (Prims.of_int (129)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (130)) (Prims.of_int (8))
                                 (Prims.of_int (131)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvshr"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (130))
                                               (Prims.of_int (8))
                                               (Prims.of_int (131))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (130))
                                         (Prims.of_int (8))
                                         (Prims.of_int (130))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (131))
                                           (Prims.of_int (8))
                                           (Prims.of_int (131))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (arith_expr_to_bv e1)
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.BV.fst"
                                            (Prims.of_int (131))
                                            (Prims.of_int (8))
                                            (Prims.of_int (131))
                                            (Prims.of_int (27)))))))
                     | FStar_Tactics_Result.Failed (e2, ps'1) ->
                         FStar_Tactics_Result.Failed (e2, ps'1)))
           | FStar_Tactics_Result.Failed (e2, ps') ->
               FStar_Tactics_Result.Failed (e2, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Land (e1, e2))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logand"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (133)) (Prims.of_int (8))
                               (Prims.of_int (133)) (Prims.of_int (36))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (134)) (Prims.of_int (8))
                                 (Prims.of_int (136)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvand"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (134))
                                               (Prims.of_int (8))
                                               (Prims.of_int (136))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (134))
                                         (Prims.of_int (8))
                                         (Prims.of_int (134))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (135))
                                           (Prims.of_int (8))
                                           (Prims.of_int (136))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (135))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (136))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (135))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (135))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (136))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (136))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (136))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (136))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.Land (e1, e2) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logand"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (133)) (Prims.of_int (8))
                               (Prims.of_int (133)) (Prims.of_int (36))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (134)) (Prims.of_int (8))
                                 (Prims.of_int (136)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvand"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (134))
                                               (Prims.of_int (8))
                                               (Prims.of_int (136))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (134))
                                         (Prims.of_int (8))
                                         (Prims.of_int (134))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (135))
                                           (Prims.of_int (8))
                                           (Prims.of_int (136))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (135))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (136))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (135))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (135))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (136))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (136))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (136))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (136))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lxor (e1, e2))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logxor"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (138)) (Prims.of_int (8))
                               (Prims.of_int (138)) (Prims.of_int (36))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (139)) (Prims.of_int (8))
                                 (Prims.of_int (141)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvxor"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (139))
                                               (Prims.of_int (8))
                                               (Prims.of_int (141))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (139))
                                         (Prims.of_int (8))
                                         (Prims.of_int (139))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (140))
                                           (Prims.of_int (8))
                                           (Prims.of_int (141))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (140))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (141))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (140))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (140))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.Lxor (e1, e2) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logxor"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (138)) (Prims.of_int (8))
                               (Prims.of_int (138)) (Prims.of_int (36))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (139)) (Prims.of_int (8))
                                 (Prims.of_int (141)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvxor"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (139))
                                               (Prims.of_int (8))
                                               (Prims.of_int (141))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (139))
                                         (Prims.of_int (8))
                                         (Prims.of_int (139))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (140))
                                           (Prims.of_int (8))
                                           (Prims.of_int (141))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (140))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (141))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (140))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (140))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (141))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lor (e1, e2)) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logor"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (143)) (Prims.of_int (8))
                               (Prims.of_int (143)) (Prims.of_int (35))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (144)) (Prims.of_int (8))
                                 (Prims.of_int (146)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvor"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (144))
                                               (Prims.of_int (8))
                                               (Prims.of_int (146))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (144))
                                         (Prims.of_int (8))
                                         (Prims.of_int (144))
                                         (Prims.of_int (32))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (145))
                                           (Prims.of_int (8))
                                           (Prims.of_int (146))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (145))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (146))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (145))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (145))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (146))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (146))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (146))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (146))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.Lor (e1, e2) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_logor"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (143)) (Prims.of_int (8))
                               (Prims.of_int (143)) (Prims.of_int (35))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (144)) (Prims.of_int (8))
                                 (Prims.of_int (146)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvor"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (144))
                                               (Prims.of_int (8))
                                               (Prims.of_int (146))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (144))
                                         (Prims.of_int (8))
                                         (Prims.of_int (144))
                                         (Prims.of_int (32))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (145))
                                           (Prims.of_int (8))
                                           (Prims.of_int (146))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (145))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (146))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (145))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (145))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (146))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (146))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (146))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (146))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Ladd (e1, e2))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_add"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (148)) (Prims.of_int (8))
                               (Prims.of_int (148)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (149)) (Prims.of_int (8))
                                 (Prims.of_int (151)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvadd"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (149))
                                               (Prims.of_int (8))
                                               (Prims.of_int (151))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (149))
                                         (Prims.of_int (8))
                                         (Prims.of_int (149))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (150))
                                           (Prims.of_int (8))
                                           (Prims.of_int (151))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (150))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (151))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (150))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (150))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (151))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (151))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (151))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (151))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.Ladd (e1, e2) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_add"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (148)) (Prims.of_int (8))
                               (Prims.of_int (148)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (149)) (Prims.of_int (8))
                                 (Prims.of_int (151)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvadd"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (149))
                                               (Prims.of_int (8))
                                               (Prims.of_int (151))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (149))
                                         (Prims.of_int (8))
                                         (Prims.of_int (149))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (150))
                                           (Prims.of_int (8))
                                           (Prims.of_int (151))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (150))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (151))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (150))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (150))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (151))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (151))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (151))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (151))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.NatToBv (FStar_Reflection_Arith.Lsub (e1, e2))
        ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_sub"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (153)) (Prims.of_int (8))
                               (Prims.of_int (153)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (154)) (Prims.of_int (8))
                                 (Prims.of_int (156)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvsub"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (154))
                                               (Prims.of_int (8))
                                               (Prims.of_int (156))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (154))
                                         (Prims.of_int (8))
                                         (Prims.of_int (154))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (155))
                                           (Prims.of_int (8))
                                           (Prims.of_int (156))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (155))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (156))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (155))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (155))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | FStar_Reflection_Arith.Lsub (e1, e2) ->
        (fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "BV"; "int2bv_sub"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (153)) (Prims.of_int (8))
                               (Prims.of_int (153)) (Prims.of_int (33))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (154)) (Prims.of_int (8))
                                 (Prims.of_int (156)) (Prims.of_int (27)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "BV";
                                       "cong_bvsub"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (154))
                                               (Prims.of_int (8))
                                               (Prims.of_int (156))
                                               (Prims.of_int (27))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (154))
                                         (Prims.of_int (8))
                                         (Prims.of_int (154))
                                         (Prims.of_int (33))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (155))
                                           (Prims.of_int (8))
                                           (Prims.of_int (156))
                                           (Prims.of_int (27)))))
                          with
                          | true ->
                              (match (arith_expr_to_bv e1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (155))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (156))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (155))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (155))
                                                   (Prims.of_int (27))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (27)))))
                                    with
                                    | true ->
                                        (arith_expr_to_bv e2)
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (27)))))))
                               | FStar_Tactics_Result.Failed (e3, ps'2) ->
                                   FStar_Tactics_Result.Failed (e3, ps'2)))
                     | FStar_Tactics_Result.Failed (e3, ps'1) ->
                         FStar_Tactics_Result.Failed (e3, ps'1)))
           | FStar_Tactics_Result.Failed (e3, ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
    | uu___ -> FStar_Tactics_Derived.trefl ()
let (arith_to_bv_tac :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         fun ps ->
           match (FStar_Tactics_Builtins.norm
                    [FStar_Pervasives.delta_only ["FStar.BV.bvult"]])
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (161)) (Prims.of_int (4))
                               (Prims.of_int (161)) (Prims.of_int (40))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (162)) (Prims.of_int (4))
                                 (Prims.of_int (175)) (Prims.of_int (65)))))
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
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (162))
                                               (Prims.of_int (4))
                                               (Prims.of_int (175))
                                               (Prims.of_int (65))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (162))
                                         (Prims.of_int (12))
                                         (Prims.of_int (162))
                                         (Prims.of_int (23))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (163))
                                           (Prims.of_int (4))
                                           (Prims.of_int (175))
                                           (Prims.of_int (65)))))
                          with
                          | true ->
                              (match (FStar_Reflection_Formula.term_as_formula
                                        a1)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (163))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (65))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (163))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (163))
                                                   (Prims.of_int (29))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (164))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (175))
                                                     (Prims.of_int (65)))))
                                    with
                                    | true ->
                                        ((match a2 with
                                          | FStar_Reflection_Formula.Comp
                                              (FStar_Reflection_Formula.Eq
                                               uu___2, l, r)
                                              ->
                                              (fun ps1 ->
                                                 match (FStar_Reflection_Arith.run_tm
                                                          (FStar_Reflection_Arith.as_arith_expr
                                                             l))
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (41))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a3, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (52)))))
                                                      with
                                                      | true ->
                                                          ((match a3 with
                                                            | FStar_Pervasives.Inl
                                                                s ->
                                                                (fun ps2 ->
                                                                   match 
                                                                    (FStar_Tactics_Builtins.dump
                                                                    s)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (18)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Derived.trefl
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (18)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                            | FStar_Pervasives.Inr
                                                                e ->
                                                                FStar_Tactics_Derived.seq
                                                                  (fun uu___3
                                                                    ->
                                                                    arith_expr_to_bv
                                                                    e)
                                                                  FStar_Tactics_Derived.trefl))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (52)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3))
                                          | uu___2 ->
                                              FStar_Tactics_Derived.fail
                                                (Prims.strcat
                                                   "arith_to_bv_tac: unexpected: "
                                                   (FStar_Reflection_Builtins.term_to_string
                                                      a1))))
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (164))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (175))
                                                      (Prims.of_int (65)))))))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (bv_tac :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         fun ps ->
           match (FStar_Tactics_Derived.mapply
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "Tactics"; "BV"; "eq_to_bv"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (182)) (Prims.of_int (2))
                               (Prims.of_int (182)) (Prims.of_int (20))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (183)) (Prims.of_int (2))
                                 (Prims.of_int (188)) (Prims.of_int (8)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.mapply
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar"; "Tactics"; "BV"; "trans"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (183))
                                               (Prims.of_int (2))
                                               (Prims.of_int (188))
                                               (Prims.of_int (8))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (183))
                                         (Prims.of_int (2))
                                         (Prims.of_int (183))
                                         (Prims.of_int (17))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (184))
                                           (Prims.of_int (2))
                                           (Prims.of_int (188))
                                           (Prims.of_int (8)))))
                          with
                          | true ->
                              (match (arith_to_bv_tac ())
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (184))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (188))
                                                         (Prims.of_int (8))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (184))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (184))
                                                   (Prims.of_int (20))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (185))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (188))
                                                     (Prims.of_int (8)))))
                                    with
                                    | true ->
                                        (match (arith_to_bv_tac ())
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.BV.fst"
                                                                   (Prims.of_int (185))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (188))
                                                                   (Prims.of_int (8))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.BV.fst"
                                                             (Prims.of_int (185))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (185))
                                                             (Prims.of_int (20))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a3, ps'3) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.BV.fst"
                                                               (Prims.of_int (186))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (188))
                                                               (Prims.of_int (8)))))
                                              with
                                              | true ->
                                                  (match (FStar_Tactics_Builtins.set_options
                                                            "--smtencoding.elim_box true")
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (43))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a4, ps'4) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'4
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.delta])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (14))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a5, ps'5)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8)))))
                                                                  with
                                                                  | true ->
                                                                    (FStar_Tactics_Derived.smt
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (8)))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'5) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'5)))
                                                   | FStar_Tactics_Result.Failed
                                                       (e, ps'4) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'4)))
                                         | FStar_Tactics_Result.Failed
                                             (e, ps'3) ->
                                             FStar_Tactics_Result.Failed
                                               (e, ps'3)))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (bv_tac_lt :
  Prims.int ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun n ->
    FStar_Tactics_Derived.focus
      (fun uu___ ->
         fun ps ->
           match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.BV.fst"
                                  (Prims.of_int (192)) (Prims.of_int (11))
                                  (Prims.of_int (192)) (Prims.of_int (39))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.BV.fst"
                            (Prims.of_int (193)) (Prims.of_int (2))
                            (Prims.of_int (198)) (Prims.of_int (8)))))
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
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (192))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (192))
                                                   (Prims.of_int (39))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.BV.fst"
                                             (Prims.of_int (193))
                                             (Prims.of_int (2))
                                             (Prims.of_int (198))
                                             (Prims.of_int (8))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.BV.fst"
                                       (Prims.of_int (193))
                                       (Prims.of_int (10))
                                       (Prims.of_int (193))
                                       (Prims.of_int (48))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (194)) (Prims.of_int (2))
                                 (Prims.of_int (198)) (Prims.of_int (8)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Derived.mk_app
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "BV";
                                          "trans_lt2"])))
                                 [((FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_Const
                                         (FStar_Reflection_Data.C_Int n))),
                                    FStar_Reflection_Data.Q_Implicit)]))
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
                                                                 "FStar.Tactics.BV.fst"
                                                                 (Prims.of_int (192))
                                                                 (Prims.of_int (11))
                                                                 (Prims.of_int (192))
                                                                 (Prims.of_int (39))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.BV.fst"
                                                           (Prims.of_int (193))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (8))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (193))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (193))
                                                     (Prims.of_int (48))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (194))
                                               (Prims.of_int (2))
                                               (Prims.of_int (198))
                                               (Prims.of_int (8))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (194))
                                         (Prims.of_int (2))
                                         (Prims.of_int (194))
                                         (Prims.of_int (15))))))
                     with
                     | FStar_Tactics_Result.Success (a, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (195))
                                           (Prims.of_int (2))
                                           (Prims.of_int (198))
                                           (Prims.of_int (8)))))
                          with
                          | true ->
                              (match (arith_to_bv_tac ())
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (195))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (198))
                                                         (Prims.of_int (8))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (195))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (195))
                                                   (Prims.of_int (20))))))
                               with
                               | FStar_Tactics_Result.Success (a1, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (196))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (198))
                                                     (Prims.of_int (8)))))
                                    with
                                    | true ->
                                        (match (arith_to_bv_tac ())
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.BV.fst"
                                                                   (Prims.of_int (196))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (198))
                                                                   (Prims.of_int (8))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.BV.fst"
                                                             (Prims.of_int (196))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (196))
                                                             (Prims.of_int (20))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a2, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.BV.fst"
                                                               (Prims.of_int (197))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (198))
                                                               (Prims.of_int (8)))))
                                              with
                                              | true ->
                                                  (match (FStar_Tactics_Builtins.set_options
                                                            "--smtencoding.elim_box true")
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (8))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (43))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a3, ps'3) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'3
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (8)))))
                                                        with
                                                        | true ->
                                                            (FStar_Tactics_Derived.smt
                                                               ())
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.BV.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (8)))))))
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
                         FStar_Tactics_Result.Failed (e, ps'))))
let (to_bv_tac :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.focus
      (fun uu___1 ->
         fun ps ->
           match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["FStar"; "Tactics"; "BV"; "eq_to_bv"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.BV.fst"
                               (Prims.of_int (202)) (Prims.of_int (2))
                               (Prims.of_int (202)) (Prims.of_int (25))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.BV.fst"
                                 (Prims.of_int (203)) (Prims.of_int (2))
                                 (Prims.of_int (205)) (Prims.of_int (20)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.apply_lemma
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar"; "Tactics"; "BV"; "trans"]))))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.BV.fst"
                                               (Prims.of_int (203))
                                               (Prims.of_int (2))
                                               (Prims.of_int (205))
                                               (Prims.of_int (20))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "FStar.Tactics.BV.fst"
                                         (Prims.of_int (203))
                                         (Prims.of_int (2))
                                         (Prims.of_int (203))
                                         (Prims.of_int (22))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.BV.fst"
                                           (Prims.of_int (204))
                                           (Prims.of_int (2))
                                           (Prims.of_int (205))
                                           (Prims.of_int (20)))))
                          with
                          | true ->
                              (match (arith_to_bv_tac ())
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.BV.fst"
                                                         (Prims.of_int (204))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (20))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.BV.fst"
                                                   (Prims.of_int (204))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (204))
                                                   (Prims.of_int (20))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.BV.fst"
                                                     (Prims.of_int (205))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (205))
                                                     (Prims.of_int (20)))))
                                    with
                                    | true ->
                                        (arith_to_bv_tac ())
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.BV.fst"
                                                      (Prims.of_int (205))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (205))
                                                      (Prims.of_int (20)))))))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))