open Prims
let (is_arith_goal :
  unit ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Arith.fst"
                          (Prims.of_int (24)) (Prims.of_int (12))
                          (Prims.of_int (24)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Arith.fst"
                            (Prims.of_int (25)) (Prims.of_int (4))
                            (Prims.of_int (27)) (Prims.of_int (16)))))
           with
           | true ->
               (match (FStar_Reflection_Arith.run_tm
                         (FStar_Reflection_Arith.is_arith_prop a))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Arith.fst"
                                          (Prims.of_int (25))
                                          (Prims.of_int (4))
                                          (Prims.of_int (27))
                                          (Prims.of_int (16))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Arith.fst"
                                    (Prims.of_int (25)) (Prims.of_int (10))
                                    (Prims.of_int (25)) (Prims.of_int (34))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Arith.fst"
                                      (Prims.of_int (25)) (Prims.of_int (4))
                                      (Prims.of_int (27)) (Prims.of_int (16)))))
                     with
                     | true ->
                         ((match a1 with
                           | FStar_Pervasives.Inr uu___1 ->
                               (fun s ->
                                  FStar_Tactics_Result.Success (true, s))
                           | uu___1 ->
                               (fun s ->
                                  FStar_Tactics_Result.Success (false, s))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Arith.fst"
                                       (Prims.of_int (25)) (Prims.of_int (4))
                                       (Prims.of_int (27))
                                       (Prims.of_int (16)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (split_arith :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (is_arith_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Arith.fst"
                          (Prims.of_int (31)) (Prims.of_int (7))
                          (Prims.of_int (31)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Arith.fst"
                            (Prims.of_int (31)) (Prims.of_int (4))
                            (Prims.of_int (52)) (Prims.of_int (7)))))
           with
           | true ->
               (if a
                then
                  (fun ps1 ->
                     match (FStar_Tactics_Builtins.prune "")
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Arith.fst"
                                         (Prims.of_int (33))
                                         (Prims.of_int (8))
                                         (Prims.of_int (33))
                                         (Prims.of_int (16))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Arith.fst"
                                           (Prims.of_int (34))
                                           (Prims.of_int (8))
                                           (Prims.of_int (35))
                                           (Prims.of_int (14)))))
                          with
                          | true ->
                              (match (FStar_Tactics_Builtins.addns "Prims")
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Arith.fst"
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (35))
                                                         (Prims.of_int (14))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (34))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (34))
                                                   (Prims.of_int (21))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Arith.fst"
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (14)))))
                                    with
                                    | true ->
                                        (FStar_Tactics_Derived.smt ())
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Arith.fst"
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (14)))))))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.cur_goal ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Arith.fst"
                                         (Prims.of_int (38))
                                         (Prims.of_int (16))
                                         (Prims.of_int (38))
                                         (Prims.of_int (27))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Arith.fst"
                                           (Prims.of_int (39))
                                           (Prims.of_int (8))
                                           (Prims.of_int (51))
                                           (Prims.of_int (14)))))
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
                                                         "FStar.Tactics.Arith.fst"
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (51))
                                                         (Prims.of_int (14))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Arith.fst"
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (39))
                                                   (Prims.of_int (31))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Arith.fst"
                                                     (Prims.of_int (39))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (14)))))
                                    with
                                    | true ->
                                        ((match a2 with
                                          | FStar_Reflection_Formula.True_ ->
                                              FStar_Tactics_Derived.trivial
                                                ()
                                          | FStar_Reflection_Formula.And
                                              (l, r) ->
                                              FStar_Tactics_Derived.seq
                                                FStar_Tactics_Logic.split
                                                split_arith
                                          | FStar_Reflection_Formula.Implies
                                              (p, q) ->
                                              (fun ps2 ->
                                                 match (FStar_Tactics_Logic.implies_intro
                                                          ())
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (36))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a3, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (36)))))
                                                      with
                                                      | true ->
                                                          (FStar_Tactics_Derived.seq
                                                             split_arith
                                                             FStar_Tactics_Logic.l_revert)
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (36)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3))
                                          | FStar_Reflection_Formula.Forall
                                              (x, p) ->
                                              (fun ps2 ->
                                                 match (FStar_Tactics_Logic.forall_intros
                                                          ())
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (37))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a3, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (55)))))
                                                      with
                                                      | true ->
                                                          (FStar_Tactics_Derived.seq
                                                             split_arith
                                                             (fun uu___2 ->
                                                                FStar_Tactics_Logic.l_revert_all
                                                                  a3))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Arith.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (55)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3))
                                          | uu___2 ->
                                              (fun s ->
                                                 FStar_Tactics_Result.Success
                                                   ((), s))))
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Arith.fst"
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (51))
                                                      (Prims.of_int (14)))))))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Arith.fst"
                             (Prims.of_int (31)) (Prims.of_int (4))
                             (Prims.of_int (52)) (Prims.of_int (7)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')