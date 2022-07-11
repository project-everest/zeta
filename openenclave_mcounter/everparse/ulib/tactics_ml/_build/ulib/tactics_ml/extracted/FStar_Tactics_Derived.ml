open Prims
exception Goal_not_trivial 
let (uu___is_Goal_not_trivial : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Goal_not_trivial -> true | uu___ -> false
let (goals :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.goal Prims.list FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Effect.get ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (30)) (Prims.of_int (42))
                          (Prims.of_int (30)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (30)) (Prims.of_int (33))
                            (Prims.of_int (30)) (Prims.of_int (50)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goals_of a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (30)) (Prims.of_int (33))
                               (Prims.of_int (30)) (Prims.of_int (50))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (smt_goals :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.goal Prims.list FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Effect.get ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (31)) (Prims.of_int (50))
                          (Prims.of_int (31)) (Prims.of_int (58))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (31)) (Prims.of_int (37))
                            (Prims.of_int (31)) (Prims.of_int (58)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.smt_goals_of a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (31)) (Prims.of_int (37))
                               (Prims.of_int (31)) (Prims.of_int (58))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let fail :
  'a .
    Prims.string ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun m -> FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m)
let fail_silently :
  'a .
    Prims.string ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun m ->
    fun ps ->
      match (FStar_Tactics_Builtins.set_urgency Prims.int_zero)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (37)) (Prims.of_int (2))
                          (Prims.of_int (37)) (Prims.of_int (15))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (38)) (Prims.of_int (2))
                            (Prims.of_int (38)) (Prims.of_int (28)))))
           with
           | true ->
               (FStar_Tactics_Effect.raise
                  (FStar_Tactics_Common.TacticFailure m))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (38)) (Prims.of_int (2))
                             (Prims.of_int (38)) (Prims.of_int (28)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (_cur_goal :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.goal FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (42)) (Prims.of_int (10))
                          (Prims.of_int (42)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (42)) (Prims.of_int (4))
                            (Prims.of_int (44)) (Prims.of_int (15)))))
           with
           | true ->
               ((match a with
                 | [] -> fail "no more goals"
                 | g::uu___1 ->
                     (fun s -> FStar_Tactics_Result.Success (g, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (42)) (Prims.of_int (4))
                             (Prims.of_int (44)) (Prims.of_int (15)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cur_env :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.env FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (47)) (Prims.of_int (36))
                          (Prims.of_int (47)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (47)) (Prims.of_int (27))
                            (Prims.of_int (47)) (Prims.of_int (50)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_env a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (47)) (Prims.of_int (27))
                               (Prims.of_int (47)) (Prims.of_int (50))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cur_goal :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.typ FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (50)) (Prims.of_int (38))
                          (Prims.of_int (50)) (Prims.of_int (52))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (50)) (Prims.of_int (28))
                            (Prims.of_int (50)) (Prims.of_int (52)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_type a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (50)) (Prims.of_int (28))
                               (Prims.of_int (50)) (Prims.of_int (52))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cur_witness :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (53)) (Prims.of_int (45))
                          (Prims.of_int (53)) (Prims.of_int (59))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (53)) (Prims.of_int (32))
                            (Prims.of_int (53)) (Prims.of_int (59)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_witness a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (53)) (Prims.of_int (32))
                               (Prims.of_int (53)) (Prims.of_int (59))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cur_goal_safe :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.goal FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (FStar_Tactics_Effect.get ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (60)) (Prims.of_int (9))
                                      (Prims.of_int (60)) (Prims.of_int (26))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (60)) (Prims.of_int (18))
                                (Prims.of_int (60)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (60)) (Prims.of_int (9))
                                  (Prims.of_int (60)) (Prims.of_int (26)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((FStar_Tactics_Types.goals_of a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (60)) (Prims.of_int (9))
                                     (Prims.of_int (60)) (Prims.of_int (26))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (60)) (Prims.of_int (3))
                            (Prims.of_int (61)) (Prims.of_int (16)))))
           with
           | true ->
               ((match a with
                 | g::uu___1 ->
                     (fun s -> FStar_Tactics_Result.Success (g, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (60)) (Prims.of_int (3))
                             (Prims.of_int (61)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cur_binders :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binders FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (65)) (Prims.of_int (19))
                          (Prims.of_int (65)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (65)) (Prims.of_int (4))
                            (Prims.of_int (65)) (Prims.of_int (31)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Builtins.binders_of_env a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (65)) (Prims.of_int (4))
                               (Prims.of_int (65)) (Prims.of_int (31))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      (unit ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun pol ->
    fun f ->
      fun ps ->
        match (FStar_Tactics_Builtins.get_guard_policy ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (69)) (Prims.of_int (18))
                            (Prims.of_int (69)) (Prims.of_int (37))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (70)) (Prims.of_int (4))
                              (Prims.of_int (73)) (Prims.of_int (5)))))
             with
             | true ->
                 (match (FStar_Tactics_Builtins.set_guard_policy pol)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (70))
                                            (Prims.of_int (4))
                                            (Prims.of_int (73))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (70)) (Prims.of_int (4))
                                      (Prims.of_int (70)) (Prims.of_int (24))))))
                  with
                  | FStar_Tactics_Result.Success (a2, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (71))
                                        (Prims.of_int (4))
                                        (Prims.of_int (73))
                                        (Prims.of_int (5)))))
                       with
                       | true ->
                           (match (f ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (73))
                                                      (Prims.of_int (5))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (71))
                                                (Prims.of_int (12))
                                                (Prims.of_int (71))
                                                (Prims.of_int (16))))))
                            with
                            | FStar_Tactics_Result.Success (a3, ps'2) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'2
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (72))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (73))
                                                  (Prims.of_int (5)))))
                                 with
                                 | true ->
                                     (match (FStar_Tactics_Builtins.set_guard_policy
                                               a1)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (72))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (73))
                                                                (Prims.of_int (5))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (28))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a4, ps'3) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'3
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (9)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 (a3,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (9))))))))
                                      | FStar_Tactics_Result.Failed (e, ps'3)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'3)))
                            | FStar_Tactics_Result.Failed (e, ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (exact :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true false t)
let (exact_with_ref :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true true t)
let (trivial :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.norm
               [FStar_Pervasives.iota;
               FStar_Pervasives.zeta;
               FStar_Pervasives.reify_;
               FStar_Pervasives.delta;
               FStar_Pervasives.primops;
               FStar_Pervasives.simplify;
               FStar_Pervasives.unmeta])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (87)) (Prims.of_int (2))
                          (Prims.of_int (87)) (Prims.of_int (61))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (88)) (Prims.of_int (2))
                            (Prims.of_int (91)) (Prims.of_int (31)))))
           with
           | true ->
               (match (cur_goal ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (88))
                                          (Prims.of_int (2))
                                          (Prims.of_int (91))
                                          (Prims.of_int (31))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (88)) (Prims.of_int (10))
                                    (Prims.of_int (88)) (Prims.of_int (21))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (89)) (Prims.of_int (2))
                                      (Prims.of_int (91)) (Prims.of_int (31)))))
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
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (89))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (91))
                                                    (Prims.of_int (31))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (89))
                                              (Prims.of_int (8))
                                              (Prims.of_int (89))
                                              (Prims.of_int (25))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (89))
                                                (Prims.of_int (2))
                                                (Prims.of_int (91))
                                                (Prims.of_int (31)))))
                               with
                               | true ->
                                   ((match a2 with
                                     | FStar_Reflection_Formula.True_ ->
                                         exact
                                           (FStar_Reflection_Builtins.pack_ln
                                              (FStar_Reflection_Data.Tv_Const
                                                 FStar_Reflection_Data.C_Unit))
                                     | uu___1 ->
                                         FStar_Tactics_Effect.raise
                                           Goal_not_trivial))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (89))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (91))
                                                 (Prims.of_int (31)))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (dismiss :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (103)) (Prims.of_int (10))
                          (Prims.of_int (103)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (103)) (Prims.of_int (4))
                            (Prims.of_int (105)) (Prims.of_int (27)))))
           with
           | true ->
               ((match a with
                 | [] -> fail "dismiss: no more goals"
                 | uu___1::gs -> FStar_Tactics_Builtins.set_goals gs))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (103)) (Prims.of_int (4))
                             (Prims.of_int (105)) (Prims.of_int (27)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (flip :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (109)) (Prims.of_int (13))
                          (Prims.of_int (109)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (110)) (Prims.of_int (4))
                            (Prims.of_int (112)) (Prims.of_int (42)))))
           with
           | true ->
               (match (goals ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (110))
                                          (Prims.of_int (4))
                                          (Prims.of_int (112))
                                          (Prims.of_int (42))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (110)) (Prims.of_int (10))
                                    (Prims.of_int (110)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (110)) (Prims.of_int (4))
                                      (Prims.of_int (112))
                                      (Prims.of_int (42)))))
                     with
                     | true ->
                         ((match a1 with
                           | [] -> fail "flip: less than two goals"
                           | uu___1::[] -> fail "flip: less than two goals"
                           | g1::g2::gs ->
                               FStar_Tactics_Builtins.set_goals (g2 :: g1 ::
                                 gs)))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (110))
                                       (Prims.of_int (4))
                                       (Prims.of_int (112))
                                       (Prims.of_int (42)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (qed :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (116)) (Prims.of_int (10))
                          (Prims.of_int (116)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (116)) (Prims.of_int (4))
                            (Prims.of_int (118)) (Prims.of_int (32)))))
           with
           | true ->
               ((match a with
                 | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
                 | uu___1 -> fail "qed: not done!"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (116)) (Prims.of_int (4))
                             (Prims.of_int (118)) (Prims.of_int (32)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (debug :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun m ->
    fun ps ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (124)) (Prims.of_int (7))
                          (Prims.of_int (124)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (124)) (Prims.of_int (4))
                            (Prims.of_int (124)) (Prims.of_int (32)))))
           with
           | true ->
               (if a
                then FStar_Tactics_Builtins.print m
                else (fun s -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (124)) (Prims.of_int (4))
                             (Prims.of_int (124)) (Prims.of_int (32)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (smt :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (131))
                                      (Prims.of_int (10))
                                      (Prims.of_int (131))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (131)) (Prims.of_int (10))
                                (Prims.of_int (131)) (Prims.of_int (18))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (131)) (Prims.of_int (10))
                                  (Prims.of_int (131)) (Prims.of_int (32)))))
                 with
                 | true ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (131))
                                                (Prims.of_int (10))
                                                (Prims.of_int (131))
                                                (Prims.of_int (32))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (131))
                                          (Prims.of_int (20))
                                          (Prims.of_int (131))
                                          (Prims.of_int (32))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (131))
                                            (Prims.of_int (10))
                                            (Prims.of_int (131))
                                            (Prims.of_int (32)))))
                           with
                           | true ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (131))
                                               (Prims.of_int (10))
                                               (Prims.of_int (131))
                                               (Prims.of_int (32))))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (131)) (Prims.of_int (4))
                            (Prims.of_int (137)) (Prims.of_int (11)))))
           with
           | true ->
               ((match a with
                 | ([], uu___1) -> fail "smt: no active goals"
                 | (g::gs, gs') ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.set_goals gs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (135))
                                            (Prims.of_int (8))
                                            (Prims.of_int (135))
                                            (Prims.of_int (20))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (136))
                                              (Prims.of_int (8))
                                              (Prims.of_int (136))
                                              (Prims.of_int (32)))))
                             with
                             | true ->
                                 (FStar_Tactics_Builtins.set_smt_goals (g ::
                                    gs'))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (136))
                                               (Prims.of_int (8))
                                               (Prims.of_int (136))
                                               (Prims.of_int (32)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (131)) (Prims.of_int (4))
                             (Prims.of_int (137)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (idtac :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> fun s -> FStar_Tactics_Result.Success ((), s)
let (later :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (143)) (Prims.of_int (10))
                          (Prims.of_int (143)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (143)) (Prims.of_int (4))
                            (Prims.of_int (145)) (Prims.of_int (33)))))
           with
           | true ->
               ((match a with
                 | g::gs ->
                     FStar_Tactics_Builtins.set_goals
                       (FStar_List_Tot_Base.op_At gs [g])
                 | uu___1 -> fail "later: no goals"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (143)) (Prims.of_int (4))
                             (Prims.of_int (145)) (Prims.of_int (33)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (apply :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply true false t
let (apply_noinst :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply true true t
let (apply_lemma :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma false false t
let (trefl :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Builtins.t_trefl false
let (trefl_guard :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Builtins.t_trefl true
let (commute_applied_match :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Builtins.t_commute_applied_match ()
let (apply_lemma_noinst :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma true false t
let (apply_lemma_rw :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply_lemma false true t
let (apply_raw :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Builtins.t_apply false false t
let (exact_guard :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    with_policy FStar_Tactics_Types.Goal
      (fun uu___ -> FStar_Tactics_Builtins.t_exact true false t)
let (t_pointwise :
  FStar_Tactics_Types.direction ->
    (unit ->
       FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun d ->
    fun tau ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (204)) (Prims.of_int (4))
                               (Prims.of_int (204)) (Prims.of_int (18))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (206)) (Prims.of_int (2))
                         (Prims.of_int (209)) (Prims.of_int (24)))))
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
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (204))
                                                (Prims.of_int (4))
                                                (Prims.of_int (204))
                                                (Prims.of_int (18))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (206))
                                          (Prims.of_int (2))
                                          (Prims.of_int (209))
                                          (Prims.of_int (24))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (207)) (Prims.of_int (4))
                                    (Prims.of_int (207)) (Prims.of_int (10))))))
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (209)) (Prims.of_int (2))
                              (Prims.of_int (209)) (Prims.of_int (24)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.ctrl_rewrite d
                    (fun t ->
                       fun s ->
                         FStar_Tactics_Result.Success
                           ((true, FStar_Tactics_Types.Continue), s))
                    (fun uu___ -> tau ()))
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
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (204))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (204))
                                                 (Prims.of_int (18))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (206))
                                           (Prims.of_int (2))
                                           (Prims.of_int (209))
                                           (Prims.of_int (24))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (207)) (Prims.of_int (4))
                                     (Prims.of_int (207)) (Prims.of_int (10))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (209)) (Prims.of_int (2))
                               (Prims.of_int (209)) (Prims.of_int (24)))))))
let (topdown_rewrite :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       (Prims.bool * Prims.int) FStar_Tactics_Result.__result)
    ->
    (unit ->
       FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun ctrl ->
    fun rw ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (234)) (Prims.of_int (6))
                               (Prims.of_int (242)) (Prims.of_int (10))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (244)) (Prims.of_int (4))
                         (Prims.of_int (244)) (Prims.of_int (33)))))
        with
        | true ->
            (FStar_Tactics_Builtins.ctrl_rewrite FStar_Tactics_Types.TopDown
               (fun t ->
                  fun ps1 ->
                    match (ctrl t)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (234))
                                        (Prims.of_int (17))
                                        (Prims.of_int (234))
                                        (Prims.of_int (23))))))
                    with
                    | FStar_Tactics_Result.Success (a, ps') ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (234))
                                          (Prims.of_int (10))
                                          (Prims.of_int (234))
                                          (Prims.of_int (14)))))
                         with
                         | true ->
                             ((match a with
                               | (b, i) ->
                                   (fun ps2 ->
                                      match (match i with
                                             | uu___ when
                                                 uu___ = Prims.int_zero ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (FStar_Tactics_Types.Continue,
                                                        s))
                                             | uu___ when
                                                 uu___ = Prims.int_one ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (FStar_Tactics_Types.Skip,
                                                        s))
                                             | uu___ when
                                                 uu___ = (Prims.of_int (2))
                                                 ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (FStar_Tactics_Types.Abort,
                                                        s))
                                             | uu___ ->
                                                 fail
                                                   "topdown_rewrite: bad value from ctrl")
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps2
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (236))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (240))
                                                          (Prims.of_int (58))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (242))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (242))
                                                            (Prims.of_int (10)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 ((b, a1),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (242))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (242))
                                                               (Prims.of_int (10))))))))
                                      | FStar_Tactics_Result.Failed (e, ps'1)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'1))))
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (234))
                                           (Prims.of_int (10))
                                           (Prims.of_int (234))
                                           (Prims.of_int (14)))))))
                    | FStar_Tactics_Result.Failed (e, ps') ->
                        FStar_Tactics_Result.Failed (e, ps')) rw)
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (234)) (Prims.of_int (6))
                                (Prims.of_int (242)) (Prims.of_int (10))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (244)) (Prims.of_int (4))
                          (Prims.of_int (244)) (Prims.of_int (33))))))
let (pointwise :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun tau -> t_pointwise FStar_Tactics_Types.BottomUp tau
let (pointwise' :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun tau -> t_pointwise FStar_Tactics_Types.TopDown tau
let (cur_module :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.name FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.top_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (250)) (Prims.of_int (13))
                          (Prims.of_int (250)) (Prims.of_int (25))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (250)) (Prims.of_int (4))
                            (Prims.of_int (250)) (Prims.of_int (25)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Builtins.moduleof a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (250)) (Prims.of_int (4))
                               (Prims.of_int (250)) (Prims.of_int (25))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (open_modules :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.name Prims.list FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.top_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (253)) (Prims.of_int (21))
                          (Prims.of_int (253)) (Prims.of_int (33))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (253)) (Prims.of_int (4))
                            (Prims.of_int (253)) (Prims.of_int (33)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Builtins.env_open_modules a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (253)) (Prims.of_int (4))
                               (Prims.of_int (253)) (Prims.of_int (33))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec repeatn :
  'a .
    Prims.int ->
      (unit ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        FStar_Tactics_Types.proofstate ->
          'a Prims.list FStar_Tactics_Result.__result
  =
  fun n ->
    fun t ->
      if n <= Prims.int_zero
      then fun s -> FStar_Tactics_Result.Success ([], s)
      else
        (fun ps ->
           match (t ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (258)) (Prims.of_int (9))
                               (Prims.of_int (258)) (Prims.of_int (13))))))
           with
           | FStar_Tactics_Result.Success (a1, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (258)) (Prims.of_int (14))
                                 (Prims.of_int (258)) (Prims.of_int (16)))))
                with
                | true ->
                    (match (repeatn (n - Prims.int_one) t)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (258))
                                               (Prims.of_int (14))
                                               (Prims.of_int (258))
                                               (Prims.of_int (16))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (258))
                                         (Prims.of_int (17))
                                         (Prims.of_int (258))
                                         (Prims.of_int (34))))))
                     with
                     | FStar_Tactics_Result.Success (a2, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (258))
                                           (Prims.of_int (14))
                                           (Prims.of_int (258))
                                           (Prims.of_int (16)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((a1 :: a2),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (258))
                                              (Prims.of_int (14))
                                              (Prims.of_int (258))
                                              (Prims.of_int (16))))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (fresh_uvar :
  FStar_Reflection_Types.typ FStar_Pervasives_Native.option ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun o ->
    fun ps ->
      match (cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (261)) (Prims.of_int (12))
                          (Prims.of_int (261)) (Prims.of_int (22))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (262)) (Prims.of_int (4))
                            (Prims.of_int (262)) (Prims.of_int (16)))))
           with
           | true ->
               (FStar_Tactics_Builtins.uvar_env a o)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (262)) (Prims.of_int (4))
                             (Prims.of_int (262)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (unify :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun t1 ->
    fun t2 ->
      fun ps ->
        match (cur_env ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (265)) (Prims.of_int (12))
                            (Prims.of_int (265)) (Prims.of_int (22))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (266)) (Prims.of_int (4))
                              (Prims.of_int (266)) (Prims.of_int (21)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.unify_env a t1 t2)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (266)) (Prims.of_int (4))
                               (Prims.of_int (266)) (Prims.of_int (21)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (unify_guard :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun t1 ->
    fun t2 ->
      fun ps ->
        match (cur_env ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (269)) (Prims.of_int (12))
                            (Prims.of_int (269)) (Prims.of_int (22))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (270)) (Prims.of_int (4))
                              (Prims.of_int (270)) (Prims.of_int (27)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.unify_guard_env a t1 t2)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (270)) (Prims.of_int (4))
                               (Prims.of_int (270)) (Prims.of_int (27)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (tmatch :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun t1 ->
    fun t2 ->
      fun ps ->
        match (cur_env ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (273)) (Prims.of_int (12))
                            (Prims.of_int (273)) (Prims.of_int (22))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (274)) (Prims.of_int (4))
                              (Prims.of_int (274)) (Prims.of_int (21)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.match_env a t1 t2)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (274)) (Prims.of_int (4))
                               (Prims.of_int (274)) (Prims.of_int (21)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let divide :
  'a 'b .
    Prims.int ->
      (unit ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        (unit ->
           FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
          ->
          FStar_Tactics_Types.proofstate ->
            ('a * 'b) FStar_Tactics_Result.__result
  =
  fun n ->
    fun l ->
      fun r ->
        fun ps ->
          match (if n < Prims.int_zero
                 then fail "divide: negative n"
                 else (fun s -> FStar_Tactics_Result.Success ((), s)))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (280)) (Prims.of_int (4))
                              (Prims.of_int (281)) (Prims.of_int (31))))))
          with
          | FStar_Tactics_Result.Success (a1, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (282)) (Prims.of_int (4))
                                (Prims.of_int (294)) (Prims.of_int (10)))))
               with
               | true ->
                   (match match (goals ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (282))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (294))
                                                          (Prims.of_int (10))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (282))
                                                    (Prims.of_int (18))
                                                    (Prims.of_int (282))
                                                    (Prims.of_int (40))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (282))
                                              (Prims.of_int (18))
                                              (Prims.of_int (282))
                                              (Prims.of_int (26))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (282))
                                                (Prims.of_int (18))
                                                (Prims.of_int (282))
                                                (Prims.of_int (40)))))
                               with
                               | true ->
                                   (match (smt_goals ())
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (282))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (282))
                                                              (Prims.of_int (40))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (282))
                                                        (Prims.of_int (28))
                                                        (Prims.of_int (282))
                                                        (Prims.of_int (40))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'2)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'2
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (282))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (282))
                                                          (Prims.of_int (40)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((a2, a3),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (282))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (282))
                                                             (Prims.of_int (40))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'2)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'2)))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)
                    with
                    | FStar_Tactics_Result.Success (a2, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (282))
                                          (Prims.of_int (4))
                                          (Prims.of_int (294))
                                          (Prims.of_int (10)))))
                         with
                         | true ->
                             ((match a2 with
                               | (gs, sgs) ->
                                   (fun ps1 ->
                                      match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (283))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (283))
                                                             (Prims.of_int (45))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Derived.fst"
                                                       (Prims.of_int (283))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (294))
                                                       (Prims.of_int (10)))))
                                      with
                                      | true ->
                                          ((match FStar_List_Tot_Base.splitAt
                                                    n gs
                                            with
                                            | (gs1, gs2) ->
                                                (fun ps2 ->
                                                   match (FStar_Tactics_Builtins.set_goals
                                                            gs1)
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (17))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a3, ps'2) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_Tactics_Builtins.set_smt_goals
                                                                    [])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (35))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a4, ps'3)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                  with
                                                                  | true ->
                                                                    (match 
                                                                    (l ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (28))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a6, a7),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (42))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a6
                                                                    with
                                                                    | (gsl,
                                                                    sgsl) ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (17))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    [])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (35))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (r ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (28))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,
                                                                    ps'9) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,
                                                                    ps'10) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a10,
                                                                    a11),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (42))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,
                                                                    ps'9) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a10
                                                                    with
                                                                    | (gsr,
                                                                    sgsr) ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    gsl gsr))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (25))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,
                                                                    ps'10) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    sgs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    sgsl sgsr)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (60))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,
                                                                    ps'11) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a5, a9),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10)))))))
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
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (283))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (283))
                                                              (Prims.of_int (45))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (283))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (294))
                                                        (Prims.of_int (10)))))))))
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (282))
                                           (Prims.of_int (4))
                                           (Prims.of_int (294))
                                           (Prims.of_int (10)))))))
                    | FStar_Tactics_Result.Failed (e, ps'1) ->
                        FStar_Tactics_Result.Failed (e, ps'1)))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let rec (iseq :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    Prims.list ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun ts ->
    match ts with
    | t::ts1 ->
        (fun ps ->
           match (divide Prims.int_one t (fun uu___ -> iseq ts1))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (298)) (Prims.of_int (23))
                               (Prims.of_int (298)) (Prims.of_int (53))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (298)) (Prims.of_int (57))
                                 (Prims.of_int (298)) (Prims.of_int (59)))))
                with
                | true ->
                    FStar_Tactics_Result.Success
                      ((),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (298)) (Prims.of_int (57))
                                    (Prims.of_int (298)) (Prims.of_int (59))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
let focus :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (304)) (Prims.of_int (10))
                          (Prims.of_int (304)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (304)) (Prims.of_int (4))
                            (Prims.of_int (311)) (Prims.of_int (9)))))
           with
           | true ->
               ((match a1 with
                 | [] -> fail "focus: no goals"
                 | g::gs ->
                     (fun ps1 ->
                        match (smt_goals ())
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (307))
                                            (Prims.of_int (18))
                                            (Prims.of_int (307))
                                            (Prims.of_int (30))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (308))
                                              (Prims.of_int (8))
                                              (Prims.of_int (311))
                                              (Prims.of_int (9)))))
                             with
                             | true ->
                                 (match (FStar_Tactics_Builtins.set_goals [g])
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (308))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (311))
                                                            (Prims.of_int (9))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (308))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (308))
                                                      (Prims.of_int (21))))))
                                  with
                                  | FStar_Tactics_Result.Success (a3, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (308))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (311))
                                                        (Prims.of_int (9)))))
                                       with
                                       | true ->
                                           (match (FStar_Tactics_Builtins.set_smt_goals
                                                     [])
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (308))
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (308))
                                                                (Prims.of_int (39))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a4, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (309))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (311))
                                                                  (Prims.of_int (9)))))
                                                 with
                                                 | true ->
                                                     (match (t ())
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (20))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a5, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9)))))
                                                           with
                                                           | true ->
                                                               (match 
                                                                  match 
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (27))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    a6 gs),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'5) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    a6)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (33)))))))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a6,
                                                                    ps'5) ->
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (62))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    a7 a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    a7)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (69)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
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
                                                                    "FStar.Tactics.Effect.fsti"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (19)))))
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
                                                                    "FStar.Tactics.Effect.fsti"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (19))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
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
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (304)) (Prims.of_int (4))
                             (Prims.of_int (311)) (Prims.of_int (9)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (dump1 :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun m -> focus (fun uu___ -> FStar_Tactics_Builtins.dump m)
let rec mapAll :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Tactics_Types.proofstate ->
        'a Prims.list FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (317)) (Prims.of_int (10))
                          (Prims.of_int (317)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (317)) (Prims.of_int (4))
                            (Prims.of_int (319)) (Prims.of_int (66)))))
           with
           | true ->
               ((match a1 with
                 | [] -> (fun s -> FStar_Tactics_Result.Success ([], s))
                 | uu___::uu___1 ->
                     (fun ps1 ->
                        match (divide Prims.int_one t
                                 (fun uu___2 -> mapAll t))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (319))
                                            (Prims.of_int (27))
                                            (Prims.of_int (319))
                                            (Prims.of_int (58))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (319))
                                              (Prims.of_int (14))
                                              (Prims.of_int (319))
                                              (Prims.of_int (66)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   (((match a2 with | (h, t1) -> h :: t1)),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (319))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (319))
                                                 (Prims.of_int (66))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (317)) (Prims.of_int (4))
                             (Prims.of_int (319)) (Prims.of_int (66)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (iterAll :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (323)) (Prims.of_int (10))
                          (Prims.of_int (323)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (323)) (Prims.of_int (4))
                            (Prims.of_int (325)) (Prims.of_int (60)))))
           with
           | true ->
               ((match a with
                 | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
                 | uu___::uu___1 ->
                     (fun ps1 ->
                        match (divide Prims.int_one t
                                 (fun uu___2 -> iterAll t))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (325))
                                            (Prims.of_int (22))
                                            (Prims.of_int (325))
                                            (Prims.of_int (54))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (325))
                                              (Prims.of_int (58))
                                              (Prims.of_int (325))
                                              (Prims.of_int (60)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   ((),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (325))
                                                 (Prims.of_int (58))
                                                 (Prims.of_int (325))
                                                 (Prims.of_int (60))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (323)) (Prims.of_int (4))
                             (Prims.of_int (325)) (Prims.of_int (60)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (iterAllSMT :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (328))
                                      (Prims.of_int (18))
                                      (Prims.of_int (328))
                                      (Prims.of_int (40))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (328)) (Prims.of_int (18))
                                (Prims.of_int (328)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (328)) (Prims.of_int (18))
                                  (Prims.of_int (328)) (Prims.of_int (40)))))
                 with
                 | true ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (328))
                                                (Prims.of_int (18))
                                                (Prims.of_int (328))
                                                (Prims.of_int (40))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (328))
                                          (Prims.of_int (28))
                                          (Prims.of_int (328))
                                          (Prims.of_int (40))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (328))
                                            (Prims.of_int (18))
                                            (Prims.of_int (328))
                                            (Prims.of_int (40)))))
                           with
                           | true ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (328))
                                               (Prims.of_int (18))
                                               (Prims.of_int (328))
                                               (Prims.of_int (40))))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (328)) (Prims.of_int (4))
                            (Prims.of_int (334)) (Prims.of_int (28)))))
           with
           | true ->
               ((match a with
                 | (gs, sgs) ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.set_goals sgs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (329))
                                            (Prims.of_int (4))
                                            (Prims.of_int (329))
                                            (Prims.of_int (17))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (330))
                                              (Prims.of_int (4))
                                              (Prims.of_int (334))
                                              (Prims.of_int (28)))))
                             with
                             | true ->
                                 (match (FStar_Tactics_Builtins.set_smt_goals
                                           [])
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (330))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (334))
                                                            (Prims.of_int (28))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (330))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (330))
                                                      (Prims.of_int (20))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (331))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (334))
                                                        (Prims.of_int (28)))))
                                       with
                                       | true ->
                                           (match (iterAll t)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (331))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (331))
                                                                (Prims.of_int (13))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (332))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (334))
                                                                  (Prims.of_int (28)))))
                                                 with
                                                 | true ->
                                                     (match match (goals ())
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (28))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a4, ps'4) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42)))))
                                                                 with
                                                                 | true ->
                                                                    (match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a4, a5),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (42))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps'4) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'4)
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28)))))
                                                           with
                                                           | true ->
                                                               ((match a4
                                                                 with
                                                                 | (gs',
                                                                    sgs') ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    gs' sgs'))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28)))))))
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
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (328)) (Prims.of_int (4))
                             (Prims.of_int (334)) (Prims.of_int (28)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (seq :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    ->
    (unit ->
       FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun f ->
    fun g ->
      focus
        (fun uu___ ->
           fun ps ->
             match (f ())
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (340)) (Prims.of_int (21))
                                 (Prims.of_int (340)) (Prims.of_int (25))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (340)) (Prims.of_int (27))
                                   (Prims.of_int (340)) (Prims.of_int (36)))))
                  with
                  | true ->
                      (iterAll g)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (340)) (Prims.of_int (27))
                                    (Prims.of_int (340)) (Prims.of_int (36)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (exact_args :
  FStar_Reflection_Data.aqualv Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun qs ->
    fun t ->
      focus
        (fun uu___ ->
           fun ps ->
             match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (344)) (Prims.of_int (16))
                                    (Prims.of_int (344)) (Prims.of_int (39))))))
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (345)) (Prims.of_int (8))
                              (Prims.of_int (350)) (Prims.of_int (44)))))
             with
             | true ->
                 (match (repeatn (FStar_List_Tot_Base.length qs)
                           (fun uu___1 ->
                              fresh_uvar FStar_Pervasives_Native.None))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (344))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (344))
                                                  (Prims.of_int (39))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (345))
                                            (Prims.of_int (8))
                                            (Prims.of_int (350))
                                            (Prims.of_int (44))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (345))
                                      (Prims.of_int (18))
                                      (Prims.of_int (345))
                                      (Prims.of_int (55))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (346))
                                        (Prims.of_int (8))
                                        (Prims.of_int (350))
                                        (Prims.of_int (44)))))
                       with
                       | true ->
                           (match match (FStar_Tactics_Util.zip a qs)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (346))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (350))
                                                                  (Prims.of_int (44))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (346))
                                                            (Prims.of_int (17))
                                                            (Prims.of_int (346))
                                                            (Prims.of_int (38))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (346))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (346))
                                                      (Prims.of_int (38))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (346))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (346))
                                                        (Prims.of_int (38)))))
                                       with
                                       | true ->
                                           FStar_Tactics_Result.Success
                                             ((FStar_Reflection_Derived.mk_app
                                                 t a1),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (346))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (346))
                                                           (Prims.of_int (38))))))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1)
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (347))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (350))
                                                  (Prims.of_int (44)))))
                                 with
                                 | true ->
                                     (match (exact a1)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (347))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (350))
                                                                (Prims.of_int (44))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (347))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (347))
                                                          (Prims.of_int (16))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (348))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (350))
                                                            (Prims.of_int (44)))))
                                           with
                                           | true ->
                                               (FStar_Tactics_Util.iter
                                                  (fun uv ->
                                                     if
                                                       FStar_Reflection_Derived.is_uvar
                                                         uv
                                                     then
                                                       FStar_Tactics_Builtins.unshelve
                                                         uv
                                                     else
                                                       (fun s ->
                                                          FStar_Tactics_Result.Success
                                                            ((), s)))
                                                  (FStar_List_Tot_Base.rev a))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (348))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (350))
                                                             (Prims.of_int (44)))))))
                                      | FStar_Tactics_Result.Failed (e, ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
let (exact_n :
  Prims.int ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun n ->
    fun t ->
      fun ps ->
        match (repeatn n
                 (fun uu___ ->
                    fun s ->
                      FStar_Tactics_Result.Success
                        (FStar_Reflection_Data.Q_Explicit, s)))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (354)) (Prims.of_int (15))
                            (Prims.of_int (354)) (Prims.of_int (49))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (354)) (Prims.of_int (4))
                              (Prims.of_int (354)) (Prims.of_int (51)))))
             with
             | true ->
                 (exact_args a t)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (354)) (Prims.of_int (4))
                               (Prims.of_int (354)) (Prims.of_int (51)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (ngoals :
  unit ->
    FStar_Tactics_Types.proofstate -> Prims.int FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (357)) (Prims.of_int (47))
                          (Prims.of_int (357)) (Prims.of_int (57))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (357)) (Prims.of_int (26))
                            (Prims.of_int (357)) (Prims.of_int (57)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.length a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (357)) (Prims.of_int (26))
                               (Prims.of_int (357)) (Prims.of_int (57))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (ngoals_smt :
  unit ->
    FStar_Tactics_Types.proofstate -> Prims.int FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (smt_goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (360)) (Prims.of_int (51))
                          (Prims.of_int (360)) (Prims.of_int (65))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (360)) (Prims.of_int (30))
                            (Prims.of_int (360)) (Prims.of_int (65)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.length a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (360)) (Prims.of_int (30))
                               (Prims.of_int (360)) (Prims.of_int (65))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (fresh_bv :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.bv FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.fresh ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (366)) (Prims.of_int (12))
                          (Prims.of_int (366)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (367)) (Prims.of_int (4))
                            (Prims.of_int (367)) (Prims.of_int (44)))))
           with
           | true ->
               (FStar_Tactics_Builtins.fresh_bv_named
                  (Prims.strcat "x" (Prims.string_of_int a)) t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (367)) (Prims.of_int (4))
                             (Prims.of_int (367)) (Prims.of_int (44)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (fresh_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun nm ->
    fun t ->
      fun ps ->
        match (FStar_Tactics_Builtins.fresh_bv_named nm t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (370)) (Prims.of_int (14))
                            (Prims.of_int (370)) (Prims.of_int (35))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (370)) (Prims.of_int (4))
                              (Prims.of_int (370)) (Prims.of_int (35)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((FStar_Reflection_Derived.mk_binder a),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (370)) (Prims.of_int (4))
                                 (Prims.of_int (370)) (Prims.of_int (35))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (fresh_binder :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.fresh ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (374)) (Prims.of_int (12))
                          (Prims.of_int (374)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (375)) (Prims.of_int (4))
                            (Prims.of_int (375)) (Prims.of_int (48)))))
           with
           | true ->
               (fresh_binder_named (Prims.strcat "x" (Prims.string_of_int a))
                  t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (375)) (Prims.of_int (4))
                             (Prims.of_int (375)) (Prims.of_int (48)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (fresh_implicit_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun nm ->
    fun t ->
      fun ps ->
        match (FStar_Tactics_Builtins.fresh_bv_named nm t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (378)) (Prims.of_int (23))
                            (Prims.of_int (378)) (Prims.of_int (44))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (378)) (Prims.of_int (4))
                              (Prims.of_int (378)) (Prims.of_int (44)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((FStar_Reflection_Derived.mk_implicit_binder a),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (378)) (Prims.of_int (4))
                                 (Prims.of_int (378)) (Prims.of_int (44))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (fresh_implicit_binder :
  FStar_Reflection_Types.typ ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.fresh ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (382)) (Prims.of_int (12))
                          (Prims.of_int (382)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (383)) (Prims.of_int (4))
                            (Prims.of_int (383)) (Prims.of_int (57)))))
           with
           | true ->
               (fresh_implicit_binder_named
                  (Prims.strcat "x" (Prims.string_of_int a)) t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (383)) (Prims.of_int (4))
                             (Prims.of_int (383)) (Prims.of_int (57)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (guard :
  Prims.bool ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    if Prims.op_Negation b
    then fail "guard failed"
    else (fun s -> FStar_Tactics_Result.Success ((), s))
let try_with :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      (Prims.exn ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun f ->
    fun h ->
      fun ps ->
        match (FStar_Tactics_Builtins.catch f)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (396)) (Prims.of_int (10))
                            (Prims.of_int (396)) (Prims.of_int (17))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (396)) (Prims.of_int (4))
                              (Prims.of_int (398)) (Prims.of_int (16)))))
             with
             | true ->
                 ((match a1 with
                   | FStar_Pervasives.Inl e -> h e
                   | FStar_Pervasives.Inr x ->
                       (fun s -> FStar_Tactics_Result.Success (x, s))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (396)) (Prims.of_int (4))
                               (Prims.of_int (398)) (Prims.of_int (16)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let trytac :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Tactics_Types.proofstate ->
        'a FStar_Pervasives_Native.option FStar_Tactics_Result.__result
  =
  fun t ->
    try_with
      (fun uu___ ->
         match () with
         | () ->
             (fun ps ->
                match (t ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (401)) (Prims.of_int (13))
                                    (Prims.of_int (401)) (Prims.of_int (19))))))
                with
                | FStar_Tactics_Result.Success (a1, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (401)) (Prims.of_int (8))
                                      (Prims.of_int (401))
                                      (Prims.of_int (19)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           ((FStar_Pervasives_Native.Some a1),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (401))
                                         (Prims.of_int (8))
                                         (Prims.of_int (401))
                                         (Prims.of_int (19))))))))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
      (fun uu___ ->
         fun s ->
           FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
let or_else :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      (unit ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t1 ->
    fun t2 ->
      try_with (fun uu___ -> match () with | () -> t1 ())
        (fun uu___ -> t2 ())
let op_Less_Bar_Greater :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      (unit ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        unit ->
          FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t1 -> fun t2 -> fun uu___ -> or_else t1 t2
let first :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      Prims.list ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun ts ->
    FStar_List_Tot_Base.fold_right op_Less_Bar_Greater ts
      (fun uu___ -> fail "no tactics to try") ()
let rec repeat :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Tactics_Types.proofstate ->
        'a Prims.list FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.catch t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (418)) (Prims.of_int (10))
                          (Prims.of_int (418)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (418)) (Prims.of_int (4))
                            (Prims.of_int (420)) (Prims.of_int (28)))))
           with
           | true ->
               ((match a1 with
                 | FStar_Pervasives.Inl uu___ ->
                     (fun s -> FStar_Tactics_Result.Success ([], s))
                 | FStar_Pervasives.Inr x ->
                     (fun ps1 ->
                        match (repeat t)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (420))
                                            (Prims.of_int (20))
                                            (Prims.of_int (420))
                                            (Prims.of_int (28))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (420))
                                              (Prims.of_int (17))
                                              (Prims.of_int (420))
                                              (Prims.of_int (19)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   ((x :: a2),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (420))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (420))
                                                 (Prims.of_int (19))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (418)) (Prims.of_int (4))
                             (Prims.of_int (420)) (Prims.of_int (28)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let repeat1 :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Tactics_Types.proofstate ->
        'a Prims.list FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (t ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (423)) (Prims.of_int (4))
                          (Prims.of_int (423)) (Prims.of_int (8))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (423)) (Prims.of_int (9))
                            (Prims.of_int (423)) (Prims.of_int (11)))))
           with
           | true ->
               (match (repeat t)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (423))
                                          (Prims.of_int (9))
                                          (Prims.of_int (423))
                                          (Prims.of_int (11))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (423)) (Prims.of_int (12))
                                    (Prims.of_int (423)) (Prims.of_int (20))))))
                with
                | FStar_Tactics_Result.Success (a2, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (423)) (Prims.of_int (9))
                                      (Prims.of_int (423))
                                      (Prims.of_int (11)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           ((a1 :: a2),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   ps'1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (423))
                                         (Prims.of_int (9))
                                         (Prims.of_int (423))
                                         (Prims.of_int (11))))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let repeat' :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun f ->
    fun ps ->
      match (repeat f)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (426)) (Prims.of_int (12))
                          (Prims.of_int (426)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (426)) (Prims.of_int (24))
                            (Prims.of_int (426)) (Prims.of_int (26)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (426)) (Prims.of_int (24))
                               (Prims.of_int (426)) (Prims.of_int (26))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun s ->
    fun t ->
      fun ps ->
        match (try_with (fun uu___ -> match () with | () -> cur_env ())
                 (fun uu___ -> FStar_Tactics_Builtins.top_env ()))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (430)) (Prims.of_int (8))
                            (Prims.of_int (431)) (Prims.of_int (30))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (433)) (Prims.of_int (4))
                              (Prims.of_int (433)) (Prims.of_int (23)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.norm_term_env a s t)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (433)) (Prims.of_int (4))
                               (Prims.of_int (433)) (Prims.of_int (23)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (join_all_smt_goals :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (440))
                                      (Prims.of_int (16))
                                      (Prims.of_int (440))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (440)) (Prims.of_int (16))
                                (Prims.of_int (440)) (Prims.of_int (24))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (440)) (Prims.of_int (16))
                                  (Prims.of_int (440)) (Prims.of_int (38)))))
                 with
                 | true ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (440))
                                                (Prims.of_int (16))
                                                (Prims.of_int (440))
                                                (Prims.of_int (38))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (440))
                                          (Prims.of_int (26))
                                          (Prims.of_int (440))
                                          (Prims.of_int (38))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (440))
                                            (Prims.of_int (16))
                                            (Prims.of_int (440))
                                            (Prims.of_int (38)))))
                           with
                           | true ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (440))
                                               (Prims.of_int (16))
                                               (Prims.of_int (440))
                                               (Prims.of_int (38))))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (440)) (Prims.of_int (2))
                            (Prims.of_int (446)) (Prims.of_int (20)))))
           with
           | true ->
               ((match a with
                 | (gs, sgs) ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.set_smt_goals [])
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (441))
                                            (Prims.of_int (2))
                                            (Prims.of_int (441))
                                            (Prims.of_int (18))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (442))
                                              (Prims.of_int (2))
                                              (Prims.of_int (446))
                                              (Prims.of_int (20)))))
                             with
                             | true ->
                                 (match (FStar_Tactics_Builtins.set_goals sgs)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (442))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (446))
                                                            (Prims.of_int (20))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (442))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (442))
                                                      (Prims.of_int (15))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (443))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (446))
                                                        (Prims.of_int (20)))))
                                       with
                                       | true ->
                                           (match (repeat'
                                                     FStar_Tactics_Builtins.join)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (443))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (443))
                                                                (Prims.of_int (14))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (444))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (446))
                                                                  (Prims.of_int (20)))))
                                                 with
                                                 | true ->
                                                     (match (goals ())
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (21))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20)))))
                                                           with
                                                           | true ->
                                                               (match 
                                                                  (FStar_Tactics_Builtins.set_goals
                                                                    gs)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (14))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a5,
                                                                    ps'5) ->
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (20)))))))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
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
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (440)) (Prims.of_int (2))
                             (Prims.of_int (446)) (Prims.of_int (20)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let discard :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      unit ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun tau ->
    fun uu___ ->
      fun ps ->
        match (tau ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (449)) (Prims.of_int (22))
                            (Prims.of_int (449)) (Prims.of_int (28))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (449)) (Prims.of_int (32))
                              (Prims.of_int (449)) (Prims.of_int (34)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (449)) (Prims.of_int (32))
                                 (Prims.of_int (449)) (Prims.of_int (34))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let rec repeatseq :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (trytac
               (fun uu___ ->
                  seq (discard t) (discard (fun uu___1 -> repeatseq t))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (453)) (Prims.of_int (12))
                          (Prims.of_int (453)) (Prims.of_int (82))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (453)) (Prims.of_int (86))
                            (Prims.of_int (453)) (Prims.of_int (88)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (453)) (Prims.of_int (86))
                               (Prims.of_int (453)) (Prims.of_int (88))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (tadmit :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Builtins.tadmit_t
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit))
let (admit1 :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> tadmit ()
let (admit_all :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (repeat tadmit)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (461)) (Prims.of_int (12))
                          (Prims.of_int (461)) (Prims.of_int (25))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (462)) (Prims.of_int (4))
                            (Prims.of_int (462)) (Prims.of_int (6)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (462)) (Prims.of_int (4))
                               (Prims.of_int (462)) (Prims.of_int (6))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (is_guard :
  unit ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (466)) (Prims.of_int (27))
                          (Prims.of_int (466)) (Prims.of_int (41))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (466)) (Prims.of_int (4))
                            (Prims.of_int (466)) (Prims.of_int (41)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.is_guard a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (466)) (Prims.of_int (4))
                               (Prims.of_int (466)) (Prims.of_int (41))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (skip_guard :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (is_guard ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (469)) (Prims.of_int (7))
                          (Prims.of_int (469)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (469)) (Prims.of_int (4))
                            (Prims.of_int (471)) (Prims.of_int (16)))))
           with
           | true ->
               (if a then smt () else fail "")
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (469)) (Prims.of_int (4))
                             (Prims.of_int (471)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (guards_to_smt :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (repeat skip_guard)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (474)) (Prims.of_int (12))
                          (Prims.of_int (474)) (Prims.of_int (29))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (475)) (Prims.of_int (4))
                            (Prims.of_int (475)) (Prims.of_int (6)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (475)) (Prims.of_int (4))
                               (Prims.of_int (475)) (Prims.of_int (6))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (simpl :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
let (whnf :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
let (compute :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
let (intros :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder Prims.list FStar_Tactics_Result.__result)
  = fun uu___ -> repeat FStar_Tactics_Builtins.intro
let (intros' :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (intros ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (483)) (Prims.of_int (36))
                          (Prims.of_int (483)) (Prims.of_int (45))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (483)) (Prims.of_int (49))
                            (Prims.of_int (483)) (Prims.of_int (51)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (483)) (Prims.of_int (49))
                               (Prims.of_int (483)) (Prims.of_int (51))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (destruct :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (FStar_Tactics_Builtins.t_destruct tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (484)) (Prims.of_int (37))
                          (Prims.of_int (484)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (484)) (Prims.of_int (54))
                            (Prims.of_int (484)) (Prims.of_int (56)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (484)) (Prims.of_int (54))
                               (Prims.of_int (484)) (Prims.of_int (56))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (destruct_intros :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun tm ->
    seq
      (fun uu___ ->
         fun ps ->
           match (FStar_Tactics_Builtins.t_destruct tm)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (485)) (Prims.of_int (59))
                               (Prims.of_int (485)) (Prims.of_int (72))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (485)) (Prims.of_int (76))
                                 (Prims.of_int (485)) (Prims.of_int (78)))))
                with
                | true ->
                    FStar_Tactics_Result.Success
                      ((),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (485)) (Prims.of_int (76))
                                    (Prims.of_int (485)) (Prims.of_int (78))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps')) intros'
let __cut : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let (tcut :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (491)) (Prims.of_int (12))
                          (Prims.of_int (491)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (492)) (Prims.of_int (4))
                            (Prims.of_int (494)) (Prims.of_int (12)))))
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
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (492))
                                             (Prims.of_int (4))
                                             (Prims.of_int (494))
                                             (Prims.of_int (12))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (492))
                                       (Prims.of_int (13))
                                       (Prims.of_int (492))
                                       (Prims.of_int (37))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (493)) (Prims.of_int (4))
                                 (Prims.of_int (494)) (Prims.of_int (12)))))
                with
                | true ->
                    (match (apply
                              (FStar_Reflection_Derived.mk_e_app
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Derived";
                                          "__cut"]))) [t; a]))
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
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (492))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (494))
                                                           (Prims.of_int (12))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (492))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (492))
                                                     (Prims.of_int (37))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (493))
                                               (Prims.of_int (4))
                                               (Prims.of_int (494))
                                               (Prims.of_int (12))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (493))
                                         (Prims.of_int (4))
                                         (Prims.of_int (493))
                                         (Prims.of_int (12))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (494))
                                           (Prims.of_int (4))
                                           (Prims.of_int (494))
                                           (Prims.of_int (12)))))
                          with
                          | true ->
                              (FStar_Tactics_Builtins.intro ())
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (494))
                                            (Prims.of_int (4))
                                            (Prims.of_int (494))
                                            (Prims.of_int (12)))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (pose :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (apply
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Derived"; "__cut"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (497)) (Prims.of_int (4))
                          (Prims.of_int (497)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (498)) (Prims.of_int (4))
                            (Prims.of_int (500)) (Prims.of_int (12)))))
           with
           | true ->
               (match (flip ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (498))
                                          (Prims.of_int (4))
                                          (Prims.of_int (500))
                                          (Prims.of_int (12))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (498)) (Prims.of_int (4))
                                    (Prims.of_int (498)) (Prims.of_int (11))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (499)) (Prims.of_int (4))
                                      (Prims.of_int (500))
                                      (Prims.of_int (12)))))
                     with
                     | true ->
                         (match (exact t)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (499))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (500))
                                                    (Prims.of_int (12))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (499))
                                              (Prims.of_int (4))
                                              (Prims.of_int (499))
                                              (Prims.of_int (11))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (500))
                                                (Prims.of_int (4))
                                                (Prims.of_int (500))
                                                (Prims.of_int (12)))))
                               with
                               | true ->
                                   (FStar_Tactics_Builtins.intro ())
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (500))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (500))
                                                 (Prims.of_int (12)))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (intro_as :
  Prims.string ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun s ->
    fun ps ->
      match (FStar_Tactics_Builtins.intro ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (503)) (Prims.of_int (12))
                          (Prims.of_int (503)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (504)) (Prims.of_int (4))
                            (Prims.of_int (504)) (Prims.of_int (17)))))
           with
           | true ->
               (FStar_Tactics_Builtins.rename_to a s)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (504)) (Prims.of_int (4))
                             (Prims.of_int (504)) (Prims.of_int (17)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (pose_as :
  Prims.string ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun s ->
    fun t ->
      fun ps ->
        match (pose t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (507)) (Prims.of_int (12))
                            (Prims.of_int (507)) (Prims.of_int (18))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (508)) (Prims.of_int (4))
                              (Prims.of_int (508)) (Prims.of_int (17)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.rename_to a s)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (508)) (Prims.of_int (4))
                               (Prims.of_int (508)) (Prims.of_int (17)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let for_each_binder :
  'a .
    (FStar_Reflection_Types.binder ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Tactics_Types.proofstate ->
        'a Prims.list FStar_Tactics_Result.__result
  =
  fun f ->
    fun ps ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (511)) (Prims.of_int (10))
                          (Prims.of_int (511)) (Prims.of_int (26))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (511)) (Prims.of_int (4))
                            (Prims.of_int (511)) (Prims.of_int (26)))))
           with
           | true ->
               (FStar_Tactics_Util.map f a1)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (511)) (Prims.of_int (4))
                             (Prims.of_int (511)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (revert_all :
  FStar_Reflection_Types.binders ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun bs ->
    match bs with
    | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
    | uu___::tl ->
        (fun ps ->
           match (FStar_Tactics_Builtins.revert ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (516)) (Prims.of_int (15))
                               (Prims.of_int (516)) (Prims.of_int (24))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (517)) (Prims.of_int (15))
                                 (Prims.of_int (517)) (Prims.of_int (28)))))
                with
                | true ->
                    (revert_all tl)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (517)) (Prims.of_int (15))
                                  (Prims.of_int (517)) (Prims.of_int (28)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (bv_to_term :
  FStar_Reflection_Types.bv ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  = fun bv -> FStar_Tactics_Builtins.pack (FStar_Reflection_Data.Tv_Var bv)
let (binder_to_term :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (521)) (Prims.of_int (57))
                             (Prims.of_int (521)) (Prims.of_int (73))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Derived.fst"
                       (Prims.of_int (521)) (Prims.of_int (45))
                       (Prims.of_int (521)) (Prims.of_int (90)))))
      with
      | true ->
          ((match FStar_Reflection_Builtins.inspect_binder b with
            | (bv, uu___) -> bv_to_term bv))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (521)) (Prims.of_int (57))
                              (Prims.of_int (521)) (Prims.of_int (73))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (521)) (Prims.of_int (45))
                        (Prims.of_int (521)) (Prims.of_int (90))))))
let rec (__assumption_aux :
  FStar_Reflection_Types.binders ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun bs ->
    match bs with
    | [] -> fail "no assumption matches goal"
    | b::bs1 ->
        (fun ps ->
           match (binder_to_term b)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (530)) (Prims.of_int (16))
                               (Prims.of_int (530)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (531)) (Prims.of_int (8))
                                 (Prims.of_int (534)) (Prims.of_int (27)))))
                with
                | true ->
                    (try_with (fun uu___ -> match () with | () -> exact a)
                       (fun uu___ ->
                          try_with
                            (fun uu___1 ->
                               match () with
                               | () ->
                                   (fun ps1 ->
                                      match (apply
                                               (FStar_Reflection_Builtins.pack_ln
                                                  (FStar_Reflection_Data.Tv_FVar
                                                     (FStar_Reflection_Builtins.pack_fv
                                                        ["FStar";
                                                        "Squash";
                                                        "return_squash"]))))
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (532))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (532))
                                                          (Prims.of_int (48))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (533))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (533))
                                                            (Prims.of_int (20)))))
                                           with
                                           | true ->
                                               (exact a)
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (533))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (533))
                                                             (Prims.of_int (20)))))))
                                      | FStar_Tactics_Result.Failed (e, ps'1)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'1)))
                            (fun uu___1 -> __assumption_aux bs1)))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (531)) (Prims.of_int (8))
                                  (Prims.of_int (534)) (Prims.of_int (27)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (assumption :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (537)) (Prims.of_int (21))
                          (Prims.of_int (537)) (Prims.of_int (37))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (537)) (Prims.of_int (4))
                            (Prims.of_int (537)) (Prims.of_int (37)))))
           with
           | true ->
               (__assumption_aux a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (537)) (Prims.of_int (4))
                             (Prims.of_int (537)) (Prims.of_int (37)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (destruct_equality_implication :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Formula.formula * FStar_Reflection_Types.term)
        FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Reflection_Formula.term_as_formula t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (540)) (Prims.of_int (10))
                          (Prims.of_int (540)) (Prims.of_int (27))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (540)) (Prims.of_int (4))
                            (Prims.of_int (547)) (Prims.of_int (15)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.Implies (lhs, rhs) ->
                     (fun ps1 ->
                        match (FStar_Reflection_Formula.term_as_formula' lhs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (542))
                                            (Prims.of_int (18))
                                            (Prims.of_int (542))
                                            (Prims.of_int (38))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (543))
                                              (Prims.of_int (14))
                                              (Prims.of_int (545))
                                              (Prims.of_int (19)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   (((match a1 with
                                      | FStar_Reflection_Formula.Comp
                                          (FStar_Reflection_Formula.Eq uu___,
                                           uu___1, uu___2)
                                          ->
                                          FStar_Pervasives_Native.Some
                                            (a1, rhs)
                                      | uu___ -> FStar_Pervasives_Native.None)),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (543))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (545))
                                                 (Prims.of_int (19))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          (FStar_Pervasives_Native.None, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (540)) (Prims.of_int (4))
                             (Prims.of_int (547)) (Prims.of_int (15)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (rewrite' :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater (fun uu___ -> FStar_Tactics_Builtins.rewrite b)
         (fun uu___ ->
            fun ps ->
              match (FStar_Tactics_Builtins.binder_retype b)
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (556)) (Prims.of_int (20))
                                  (Prims.of_int (556)) (Prims.of_int (35))))))
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (557)) (Prims.of_int (20))
                                    (Prims.of_int (558)) (Prims.of_int (29)))))
                   with
                   | true ->
                       (match (apply_lemma
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Derived";
                                          "__eq_sym"]))))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (557))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (558))
                                                  (Prims.of_int (29))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (557))
                                            (Prims.of_int (20))
                                            (Prims.of_int (557))
                                            (Prims.of_int (43))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (558))
                                              (Prims.of_int (20))
                                              (Prims.of_int (558))
                                              (Prims.of_int (29)))))
                             with
                             | true ->
                                 (FStar_Tactics_Builtins.rewrite b)
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (558))
                                               (Prims.of_int (20))
                                               (Prims.of_int (558))
                                               (Prims.of_int (29)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')))
      (fun uu___ -> fail "rewrite' failed") ()
let rec (try_rewrite_equality :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.binders ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun x ->
    fun bs ->
      match bs with
      | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
      | x_t::bs1 ->
          (fun ps ->
             match (FStar_Reflection_Formula.term_as_formula
                      (FStar_Reflection_Derived.type_of_binder x_t))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (566)) (Prims.of_int (20))
                                 (Prims.of_int (566)) (Prims.of_int (56))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (566)) (Prims.of_int (14))
                                   (Prims.of_int (572)) (Prims.of_int (37)))))
                  with
                  | true ->
                      ((match a with
                        | FStar_Reflection_Formula.Comp
                            (FStar_Reflection_Formula.Eq uu___, y, uu___1) ->
                            if FStar_Reflection_Builtins.term_eq x y
                            then FStar_Tactics_Builtins.rewrite x_t
                            else try_rewrite_equality x bs1
                        | uu___ -> try_rewrite_equality x bs1))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (566)) (Prims.of_int (14))
                                    (Prims.of_int (572)) (Prims.of_int (37)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec (rewrite_all_context_equalities :
  FStar_Reflection_Types.binders ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun bs ->
    match bs with
    | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
    | x_t::bs1 ->
        (fun ps ->
           match (try_with
                    (fun uu___ ->
                       match () with
                       | () -> FStar_Tactics_Builtins.rewrite x_t)
                    (fun uu___ ->
                       fun s -> FStar_Tactics_Result.Success ((), s)))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (579)) (Prims.of_int (8))
                               (Prims.of_int (579)) (Prims.of_int (40))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (580)) (Prims.of_int (8))
                                 (Prims.of_int (580)) (Prims.of_int (41)))))
                with
                | true ->
                    (rewrite_all_context_equalities bs1)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (580)) (Prims.of_int (8))
                                  (Prims.of_int (580)) (Prims.of_int (41)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (rewrite_eqs_from_context :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (584)) (Prims.of_int (35))
                          (Prims.of_int (584)) (Prims.of_int (51))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (584)) (Prims.of_int (4))
                            (Prims.of_int (584)) (Prims.of_int (51)))))
           with
           | true ->
               (rewrite_all_context_equalities a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (584)) (Prims.of_int (4))
                             (Prims.of_int (584)) (Prims.of_int (51)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (rewrite_equality :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (587)) (Prims.of_int (27))
                          (Prims.of_int (587)) (Prims.of_int (43))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (587)) (Prims.of_int (4))
                            (Prims.of_int (587)) (Prims.of_int (43)))))
           with
           | true ->
               (try_rewrite_equality t a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (587)) (Prims.of_int (4))
                             (Prims.of_int (587)) (Prims.of_int (43)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (unfold_def :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (590)) (Prims.of_int (10))
                          (Prims.of_int (590)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (590)) (Prims.of_int (4))
                            (Prims.of_int (594)) (Prims.of_int (46)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun ps1 ->
                        match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (592))
                                               (Prims.of_int (16))
                                               (Prims.of_int (592))
                                               (Prims.of_int (42))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (593))
                                         (Prims.of_int (8))
                                         (Prims.of_int (593))
                                         (Prims.of_int (30)))))
                        with
                        | true ->
                            (FStar_Tactics_Builtins.norm
                               [FStar_Pervasives.delta_fully
                                  [FStar_Reflection_Builtins.implode_qn
                                     (FStar_Reflection_Builtins.inspect_fv fv)]])
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (592))
                                                (Prims.of_int (16))
                                                (Prims.of_int (592))
                                                (Prims.of_int (42))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (593))
                                          (Prims.of_int (8))
                                          (Prims.of_int (593))
                                          (Prims.of_int (30)))))))
                 | uu___ -> fail "unfold_def: term is not a fv"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (590)) (Prims.of_int (4))
                             (Prims.of_int (594)) (Prims.of_int (46)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (l_to_r :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun lems ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (601)) (Prims.of_int (8))
                             (Prims.of_int (604)) (Prims.of_int (31))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Derived.fst"
                       (Prims.of_int (605)) (Prims.of_int (4))
                       (Prims.of_int (605)) (Prims.of_int (28)))))
      with
      | true ->
          (pointwise
             (fun uu___ ->
                fun ps1 ->
                  match (FStar_Tactics_Util.fold_left
                           (fun k ->
                              fun l ->
                                fun s ->
                                  FStar_Tactics_Result.Success
                                    ((fun uu___1 ->
                                        or_else
                                          (fun uu___2 -> apply_lemma_rw l) k),
                                      s)) trefl lems)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (601)) (Prims.of_int (8))
                                      (Prims.of_int (604))
                                      (Prims.of_int (31))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (601))
                                        (Prims.of_int (8))
                                        (Prims.of_int (604))
                                        (Prims.of_int (31)))))
                       with
                       | true ->
                           (a ())
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (601))
                                         (Prims.of_int (8))
                                         (Prims.of_int (604))
                                         (Prims.of_int (31)))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (601)) (Prims.of_int (8))
                              (Prims.of_int (604)) (Prims.of_int (31))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (605)) (Prims.of_int (4))
                        (Prims.of_int (605)) (Prims.of_int (28))))))
let (mk_squash : FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t ->
    let sq =
      FStar_Reflection_Builtins.pack_ln
        (FStar_Reflection_Data.Tv_FVar
           (FStar_Reflection_Builtins.pack_fv
              FStar_Reflection_Const.squash_qn)) in
    FStar_Reflection_Derived.mk_e_app sq [t]
let (mk_sq_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1 ->
    fun t2 ->
      let eq =
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn)) in
      mk_squash (FStar_Reflection_Derived.mk_e_app eq [t1; t2])
let (grewrite :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t1 ->
    fun t2 ->
      fun ps ->
        match (tcut (mk_sq_eq t1 t2))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (616)) (Prims.of_int (12))
                            (Prims.of_int (616)) (Prims.of_int (33))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (617)) (Prims.of_int (4))
                              (Prims.of_int (618)) (Prims.of_int (58)))))
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
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (617))
                                               (Prims.of_int (4))
                                               (Prims.of_int (618))
                                               (Prims.of_int (58))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (617))
                                         (Prims.of_int (12))
                                         (Prims.of_int (617))
                                         (Prims.of_int (45))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (618)) (Prims.of_int (4))
                                   (Prims.of_int (618)) (Prims.of_int (58)))))
                  with
                  | true ->
                      (pointwise
                         (fun uu___ ->
                            try_with
                              (fun uu___1 ->
                                 match () with
                                 | () ->
                                     exact
                                       (FStar_Reflection_Builtins.pack_ln
                                          (FStar_Reflection_Data.Tv_Var
                                             (FStar_Reflection_Derived.bv_of_binder
                                                a))))
                              (fun uu___1 -> trefl ())))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (617))
                                                (Prims.of_int (4))
                                                (Prims.of_int (618))
                                                (Prims.of_int (58))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (617))
                                          (Prims.of_int (12))
                                          (Prims.of_int (617))
                                          (Prims.of_int (45))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (618)) (Prims.of_int (4))
                                    (Prims.of_int (618)) (Prims.of_int (58))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')

let (grewrite_eq :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ps ->
      match (FStar_Reflection_Formula.term_as_formula
               (FStar_Reflection_Derived.type_of_binder b))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (625)) (Prims.of_int (8))
                          (Prims.of_int (625)) (Prims.of_int (42))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (625)) (Prims.of_int (2))
                            (Prims.of_int (637)) (Prims.of_int (7)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.Comp
                     (FStar_Reflection_Formula.Eq uu___, l, r) ->
                     (fun ps1 ->
                        match (grewrite l r)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (627))
                                            (Prims.of_int (4))
                                            (Prims.of_int (627))
                                            (Prims.of_int (16))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (628))
                                              (Prims.of_int (4))
                                              (Prims.of_int (628))
                                              (Prims.of_int (54)))))
                             with
                             | true ->
                                 (iseq
                                    [idtac;
                                    (fun uu___1 ->
                                       fun ps2 ->
                                         match (binder_to_term b)
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (628))
                                                             (Prims.of_int (34))
                                                             (Prims.of_int (628))
                                                             (Prims.of_int (52))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a2, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (628))
                                                               (Prims.of_int (28))
                                                               (Prims.of_int (628))
                                                               (Prims.of_int (52)))))
                                              with
                                              | true ->
                                                  (exact a2)
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (628))
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (628))
                                                                (Prims.of_int (52)))))))
                                         | FStar_Tactics_Result.Failed
                                             (e, ps'2) ->
                                             FStar_Tactics_Result.Failed
                                               (e, ps'2))])
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (628))
                                               (Prims.of_int (4))
                                               (Prims.of_int (628))
                                               (Prims.of_int (54)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ ->
                     (fun ps1 ->
                        match (FStar_Reflection_Formula.term_as_formula'
                                 (FStar_Reflection_Derived.type_of_binder b))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (630))
                                            (Prims.of_int (16))
                                            (Prims.of_int (630))
                                            (Prims.of_int (51))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (630))
                                              (Prims.of_int (10))
                                              (Prims.of_int (636))
                                              (Prims.of_int (56)))))
                             with
                             | true ->
                                 ((match a1 with
                                   | FStar_Reflection_Formula.Comp
                                       (FStar_Reflection_Formula.Eq uu___1,
                                        l, r)
                                       ->
                                       (fun ps2 ->
                                          match (grewrite l r)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (632))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (632))
                                                              (Prims.of_int (18))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a2, ps'2) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (633))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (634))
                                                                (Prims.of_int (56)))))
                                               with
                                               | true ->
                                                   (iseq
                                                      [idtac;
                                                      (fun uu___2 ->
                                                         fun ps3 ->
                                                           match (apply_lemma
                                                                    (
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "__un_sq_eq"]))))
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (55))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (54)))))
                                                                with
                                                                | true ->
                                                                    (
                                                                    match 
                                                                    (binder_to_term
                                                                    b)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (54))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (54))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (54)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (exact a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (54)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                           | FStar_Tactics_Result.Failed
                                                               (e, ps'3) ->
                                                               FStar_Tactics_Result.Failed
                                                                 (e, ps'3))])
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Derived.fst"
                                                                 (Prims.of_int (633))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (634))
                                                                 (Prims.of_int (56)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'2) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'2))
                                   | uu___1 ->
                                       fail
                                         "grewrite_eq: binder type is not an equality"))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (630))
                                               (Prims.of_int (10))
                                               (Prims.of_int (636))
                                               (Prims.of_int (56)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (625)) (Prims.of_int (2))
                             (Prims.of_int (637)) (Prims.of_int (7)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')


let rec (apply_squash_or_lem :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun d ->
    fun t ->
      try_with (fun uu___ -> match () with | () -> apply t)
        (fun uu___ ->
           try_with
             (fun uu___1 ->
                match () with
                | () ->
                    (fun ps ->
                       match (apply
                                (FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Builtins.pack_fv
                                         ["FStar"; "Squash"; "return_squash"]))))
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (659))
                                           (Prims.of_int (8))
                                           (Prims.of_int (659))
                                           (Prims.of_int (43))))))
                       with
                       | FStar_Tactics_Result.Success (a, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (659))
                                             (Prims.of_int (45))
                                             (Prims.of_int (659))
                                             (Prims.of_int (52)))))
                            with
                            | true ->
                                (apply t)
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (659))
                                              (Prims.of_int (45))
                                              (Prims.of_int (659))
                                              (Prims.of_int (52)))))))
                       | FStar_Tactics_Result.Failed (e, ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
             (fun uu___1 ->
                try_with (fun uu___2 -> match () with | () -> apply_lemma t)
                  (fun uu___2 ->
                     if d <= Prims.int_zero
                     then fail "mapply: out of fuel"
                     else
                       (fun ps ->
                          match match (cur_env ())
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (665))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (665))
                                                          (Prims.of_int (30))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (665))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (665))
                                                    (Prims.of_int (28))))))
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (665))
                                                      (Prims.of_int (13))
                                                      (Prims.of_int (665))
                                                      (Prims.of_int (30)))))
                                     with
                                     | true ->
                                         (FStar_Tactics_Builtins.tc a t)
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Derived.fst"
                                                       (Prims.of_int (665))
                                                       (Prims.of_int (13))
                                                       (Prims.of_int (665))
                                                       (Prims.of_int (30)))))))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (666))
                                                (Prims.of_int (4))
                                                (Prims.of_int (714))
                                                (Prims.of_int (41)))))
                               with
                               | true ->
                                   (match (FStar_Tactics_SyntaxHelpers.collect_arr
                                             a)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (666))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (714))
                                                              (Prims.of_int (41))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (666))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (666))
                                                        (Prims.of_int (31))))))
                                    with
                                    | FStar_Tactics_Result.Success (a1, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (666))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (714))
                                                          (Prims.of_int (41)))))
                                         with
                                         | true ->
                                             ((match a1 with
                                               | (tys, c) ->
                                                   (match FStar_Reflection_Builtins.inspect_comp
                                                            c
                                                    with
                                                    | FStar_Reflection_Data.C_Lemma
                                                        (pre, post, uu___4)
                                                        ->
                                                        (fun ps1 ->
                                                           match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41)))))
                                                           with
                                                           | true ->
                                                               (match 
                                                                  (norm_term
                                                                    []
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    (post,
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (35))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (31))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (38)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (38)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu___5
                                                                    ->
                                                                    fail
                                                                    "mapply: can't apply (1)"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (41)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                    | FStar_Reflection_Data.C_Total
                                                        (rt, uu___4) ->
                                                        (match FStar_Reflection_Formula.unsquash
                                                                 rt
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             rt1 ->
                                                             (fun ps1 ->
                                                                match 
                                                                  (norm_term
                                                                    [] rt1)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (33))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (43)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (43)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (33))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (40)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (40)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu___5
                                                                    ->
                                                                    fail
                                                                    "mapply: can't apply (1)"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (43)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             (fun ps1 ->
                                                                match 
                                                                  (norm_term
                                                                    [] rt)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (33))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (33))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (40)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (40)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu___5
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (48))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (apply t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (20)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                    | uu___4 ->
                                                        fail
                                                          "mapply: can't apply (2)")))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (666))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (714))
                                                           (Prims.of_int (41)))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1)))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps')))))
let (mapply :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun t -> apply_squash_or_lem (Prims.of_int (10)) t
let (admit_dump_t :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.dump "Admitting")
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (724)) (Prims.of_int (2))
                          (Prims.of_int (724)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (725)) (Prims.of_int (2))
                            (Prims.of_int (725)) (Prims.of_int (16)))))
           with
           | true ->
               (apply
                  (FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv ["Prims"; "admit"]))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (725)) (Prims.of_int (2))
                             (Prims.of_int (725)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let admit_dump : 'a . (unit -> 'a) -> unit -> 'a = fun x -> fun uu___ -> x ()
let (magic_dump_t :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.dump "Admitting")
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (732)) (Prims.of_int (2))
                          (Prims.of_int (732)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (733)) (Prims.of_int (2))
                            (Prims.of_int (735)) (Prims.of_int (4)))))
           with
           | true ->
               (match (apply
                         (FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_FVar
                               (FStar_Reflection_Builtins.pack_fv
                                  ["Prims"; "magic"]))))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (733))
                                          (Prims.of_int (2))
                                          (Prims.of_int (735))
                                          (Prims.of_int (4))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (733)) (Prims.of_int (2))
                                    (Prims.of_int (733)) (Prims.of_int (16))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (734)) (Prims.of_int (2))
                                      (Prims.of_int (735)) (Prims.of_int (4)))))
                     with
                     | true ->
                         (match (exact
                                   (FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_Const
                                         FStar_Reflection_Data.C_Unit)))
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (734))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (735))
                                                    (Prims.of_int (4))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (734))
                                              (Prims.of_int (2))
                                              (Prims.of_int (734))
                                              (Prims.of_int (13))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (735))
                                                (Prims.of_int (2))
                                                (Prims.of_int (735))
                                                (Prims.of_int (4)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (735))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (735))
                                                   (Prims.of_int (4))))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let magic_dump : 'a . 'a -> unit -> 'a = fun x -> fun uu___ -> x
let (change_with :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t1 ->
    fun t2 ->
      focus
        (fun uu___ ->
           fun ps ->
             match (grewrite t1 t2)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (742)) (Prims.of_int (8))
                                 (Prims.of_int (742)) (Prims.of_int (22))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (743)) (Prims.of_int (8))
                                   (Prims.of_int (743)) (Prims.of_int (29)))))
                  with
                  | true ->
                      (iseq [idtac; trivial])
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (743)) (Prims.of_int (8))
                                    (Prims.of_int (743)) (Prims.of_int (29)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (change_sq :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t1 ->
    FStar_Tactics_Builtins.change
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv ["Prims"; "squash"]))) 
         [t1])
let finish_by :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      match (t ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (750)) (Prims.of_int (12))
                          (Prims.of_int (750)) (Prims.of_int (16))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (751)) (Prims.of_int (4))
                            (Prims.of_int (752)) (Prims.of_int (5)))))
           with
           | true ->
               (match (or_else qed
                         (fun uu___ -> fail "finish_by: not finished"))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (751))
                                          (Prims.of_int (4))
                                          (Prims.of_int (752))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (751)) (Prims.of_int (4))
                                    (Prims.of_int (751)) (Prims.of_int (58))))))
                with
                | FStar_Tactics_Result.Success (a2, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (750)) (Prims.of_int (8))
                                      (Prims.of_int (750)) (Prims.of_int (9)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           (a1,
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   ps'1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (750))
                                         (Prims.of_int (8))
                                         (Prims.of_int (750))
                                         (Prims.of_int (9))))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let solve_then :
  'a 'b .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      ('a ->
         FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
        -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun t1 ->
    fun t2 ->
      fun ps ->
        match (FStar_Tactics_Builtins.dup ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (755)) (Prims.of_int (4))
                            (Prims.of_int (755)) (Prims.of_int (10))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (756)) (Prims.of_int (4))
                              (Prims.of_int (759)) (Prims.of_int (5)))))
             with
             | true ->
                 (match (focus (fun uu___ -> finish_by t1))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (756))
                                            (Prims.of_int (4))
                                            (Prims.of_int (759))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (756))
                                      (Prims.of_int (12))
                                      (Prims.of_int (756))
                                      (Prims.of_int (42))))))
                  with
                  | FStar_Tactics_Result.Success (a2, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (757))
                                        (Prims.of_int (4))
                                        (Prims.of_int (759))
                                        (Prims.of_int (5)))))
                       with
                       | true ->
                           (match (t2 a2)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (757))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (759))
                                                      (Prims.of_int (5))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (757))
                                                (Prims.of_int (12))
                                                (Prims.of_int (757))
                                                (Prims.of_int (16))))))
                            with
                            | FStar_Tactics_Result.Success (a3, ps'2) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'2
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (758))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (759))
                                                  (Prims.of_int (5)))))
                                 with
                                 | true ->
                                     (match (trefl ())
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (758))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (759))
                                                                (Prims.of_int (5))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (758))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (758))
                                                          (Prims.of_int (12))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a4, ps'3) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'3
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (757))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (757))
                                                            (Prims.of_int (9)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 (a3,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (757))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (757))
                                                               (Prims.of_int (9))))))))
                                      | FStar_Tactics_Result.Failed (e, ps'3)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'3)))
                            | FStar_Tactics_Result.Failed (e, ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let add_elem :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    focus
      (fun uu___ ->
         fun ps ->
           match (apply
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Builtins.pack_fv
                             ["Prims"; "Cons"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (762)) (Prims.of_int (4))
                               (Prims.of_int (762)) (Prims.of_int (17))))))
           with
           | FStar_Tactics_Result.Success (a1, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (763)) (Prims.of_int (4))
                                 (Prims.of_int (767)) (Prims.of_int (5)))))
                with
                | true ->
                    (focus
                       (fun uu___1 ->
                          fun ps1 ->
                            match (t ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (764))
                                                (Prims.of_int (14))
                                                (Prims.of_int (764))
                                                (Prims.of_int (18))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (765))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (766))
                                                  (Prims.of_int (7)))))
                                 with
                                 | true ->
                                     (match (qed ())
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (765))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (766))
                                                                (Prims.of_int (7))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (765))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (765))
                                                          (Prims.of_int (12))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (764))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (764))
                                                            (Prims.of_int (11)))))
                                           with
                                           | true ->
                                               FStar_Tactics_Result.Success
                                                 (a2,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (764))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (764))
                                                               (Prims.of_int (11))))))))
                                      | FStar_Tactics_Result.Failed (e, ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (763)) (Prims.of_int (4))
                                  (Prims.of_int (767)) (Prims.of_int (5)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let specialize :
  'a .
    'a ->
      Prims.string Prims.list ->
        unit ->
          FStar_Tactics_Types.proofstate ->
            unit FStar_Tactics_Result.__result
  =
  fun f ->
    fun l ->
      fun uu___ ->
        solve_then
          (fun uu___1 ->
             fun ps ->
               match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (786))
                                      (Prims.of_int (42))
                                      (Prims.of_int (786))
                                      (Prims.of_int (51))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (786)) (Prims.of_int (36))
                                (Prims.of_int (786)) (Prims.of_int (51)))))
               with
               | true ->
                   (exact
                      (Obj.magic
                         (failwith
                            "Cannot evaluate open quotation at runtime")))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (786))
                                       (Prims.of_int (42))
                                       (Prims.of_int (786))
                                       (Prims.of_int (51))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (786)) (Prims.of_int (36))
                                 (Prims.of_int (786)) (Prims.of_int (51)))))))
          (fun uu___1 ->
             FStar_Tactics_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
let (tlabel :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun l ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (789)) (Prims.of_int (10))
                          (Prims.of_int (789)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (789)) (Prims.of_int (4))
                            (Prims.of_int (792)) (Prims.of_int (38)))))
           with
           | true ->
               ((match a with
                 | [] -> fail "tlabel: no goals"
                 | h::t ->
                     FStar_Tactics_Builtins.set_goals
                       ((FStar_Tactics_Types.set_label l h) :: t)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (789)) (Prims.of_int (4))
                             (Prims.of_int (792)) (Prims.of_int (38)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (tlabel' :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun l ->
    fun ps ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (795)) (Prims.of_int (10))
                          (Prims.of_int (795)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (795)) (Prims.of_int (4))
                            (Prims.of_int (799)) (Prims.of_int (26)))))
           with
           | true ->
               ((match a with
                 | [] -> fail "tlabel': no goals"
                 | h::t ->
                     (fun ps1 ->
                        match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (798))
                                               (Prims.of_int (16))
                                               (Prims.of_int (798))
                                               (Prims.of_int (45))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (799))
                                         (Prims.of_int (8))
                                         (Prims.of_int (799))
                                         (Prims.of_int (26)))))
                        with
                        | true ->
                            (FStar_Tactics_Builtins.set_goals
                               ((FStar_Tactics_Types.set_label
                                   (Prims.strcat l
                                      (FStar_Tactics_Types.get_label h)) h)
                               :: t))
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (798))
                                                (Prims.of_int (16))
                                                (Prims.of_int (798))
                                                (Prims.of_int (45))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (799))
                                          (Prims.of_int (8))
                                          (Prims.of_int (799))
                                          (Prims.of_int (26)))))))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (795)) (Prims.of_int (4))
                             (Prims.of_int (799)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (focus_all :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match match (goals ())
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (802))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (802))
                                                  (Prims.of_int (39))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (802))
                                            (Prims.of_int (14))
                                            (Prims.of_int (802))
                                            (Prims.of_int (39))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (802))
                                      (Prims.of_int (15))
                                      (Prims.of_int (802))
                                      (Prims.of_int (23))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Derived.fst"
                                        (Prims.of_int (802))
                                        (Prims.of_int (14))
                                        (Prims.of_int (802))
                                        (Prims.of_int (39)))))
                       with
                       | true ->
                           (match (smt_goals ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (802))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (802))
                                                      (Prims.of_int (39))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (802))
                                                (Prims.of_int (26))
                                                (Prims.of_int (802))
                                                (Prims.of_int (38))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (802))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (802))
                                                  (Prims.of_int (39)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       ((FStar_List_Tot_Base.op_At a a1),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (802))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (802))
                                                     (Prims.of_int (39))))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (802)) (Prims.of_int (4))
                                  (Prims.of_int (802)) (Prims.of_int (39)))))
                 with
                 | true ->
                     (FStar_Tactics_Builtins.set_goals a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (802)) (Prims.of_int (4))
                                   (Prims.of_int (802)) (Prims.of_int (39)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (803)) (Prims.of_int (4))
                            (Prims.of_int (803)) (Prims.of_int (20)))))
           with
           | true ->
               (FStar_Tactics_Builtins.set_smt_goals [])
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (803)) (Prims.of_int (4))
                             (Prims.of_int (803)) (Prims.of_int (20)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec extract_nth :
  'a .
    Prims.nat ->
      'a Prims.list -> ('a * 'a Prims.list) FStar_Pervasives_Native.option
  =
  fun n ->
    fun l ->
      match (n, l) with
      | (uu___, []) -> FStar_Pervasives_Native.None
      | (uu___, hd::tl) when uu___ = Prims.int_zero ->
          FStar_Pervasives_Native.Some (hd, tl)
      | (uu___, hd::tl) ->
          (match extract_nth (n - Prims.int_one) tl with
           | FStar_Pervasives_Native.Some (hd', tl') ->
               FStar_Pervasives_Native.Some (hd', (hd :: tl'))
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (bump_nth :
  Prims.pos ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun n ->
    fun ps ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (818)) (Prims.of_int (8))
                                      (Prims.of_int (818))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (818)) (Prims.of_int (28))
                                (Prims.of_int (818)) (Prims.of_int (38))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (818)) (Prims.of_int (8))
                                  (Prims.of_int (818)) (Prims.of_int (38)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((extract_nth (n - Prims.int_one) a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (818)) (Prims.of_int (8))
                                     (Prims.of_int (818)) (Prims.of_int (38))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (818)) (Prims.of_int (2))
                            (Prims.of_int (820)) (Prims.of_int (37)))))
           with
           | true ->
               ((match a with
                 | FStar_Pervasives_Native.None ->
                     fail "bump_nth: not that many goals"
                 | FStar_Pervasives_Native.Some (h, t) ->
                     FStar_Tactics_Builtins.set_goals (h :: t)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (818)) (Prims.of_int (2))
                             (Prims.of_int (820)) (Prims.of_int (37)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (on_sort_bv :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Types.bv ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.bv FStar_Tactics_Result.__result)
  =
  fun f ->
    fun xbv ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (823)) (Prims.of_int (12))
                               (Prims.of_int (823)) (Prims.of_int (26))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (824)) (Prims.of_int (2))
                         (Prims.of_int (826)) (Prims.of_int (4)))))
        with
        | true ->
            (match match (f
                            (FStar_Reflection_Builtins.inspect_bv xbv).FStar_Reflection_Data.bv_sort)
                           (FStar_Tactics_Types.incr_depth
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
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (823))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (823))
                                                         (Prims.of_int (26))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (824))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (826))
                                                   (Prims.of_int (4))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (824))
                                             (Prims.of_int (14))
                                             (Prims.of_int (824))
                                             (Prims.of_int (46))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (824))
                                       (Prims.of_int (33))
                                       (Prims.of_int (824))
                                       (Prims.of_int (46))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (824))
                                         (Prims.of_int (14))
                                         (Prims.of_int (824))
                                         (Prims.of_int (46)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ({
                                 FStar_Reflection_Data.bv_ppname =
                                   ((FStar_Reflection_Builtins.inspect_bv xbv).FStar_Reflection_Data.bv_ppname);
                                 FStar_Reflection_Data.bv_index =
                                   ((FStar_Reflection_Builtins.inspect_bv xbv).FStar_Reflection_Data.bv_index);
                                 FStar_Reflection_Data.bv_sort = a
                               },
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (824))
                                            (Prims.of_int (14))
                                            (Prims.of_int (824))
                                            (Prims.of_int (46))))))))
                   | FStar_Tactics_Result.Failed (e, ps') ->
                       FStar_Tactics_Result.Failed (e, ps')
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (825)) (Prims.of_int (11))
                                   (Prims.of_int (825)) (Prims.of_int (22)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Builtins.pack_bv a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (825))
                                      (Prims.of_int (11))
                                      (Prims.of_int (825))
                                      (Prims.of_int (22))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (on_sort_binder :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Types.binder ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun f ->
    fun b ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (829)) (Prims.of_int (23))
                               (Prims.of_int (829)) (Prims.of_int (39))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (829)) (Prims.of_int (2))
                         (Prims.of_int (832)) (Prims.of_int (3)))))
        with
        | true ->
            ((match FStar_Reflection_Builtins.inspect_binder b with
              | (bv, (q, attrs)) ->
                  (fun ps1 ->
                     match (on_sort_bv f bv)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (830))
                                         (Prims.of_int (11))
                                         (Prims.of_int (830))
                                         (Prims.of_int (26))))))
                     with
                     | FStar_Tactics_Result.Success (a, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (831))
                                           (Prims.of_int (10))
                                           (Prims.of_int (831))
                                           (Prims.of_int (32)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Builtins.pack_binder a q
                                    attrs),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (831))
                                              (Prims.of_int (10))
                                              (Prims.of_int (831))
                                              (Prims.of_int (32))))))))
                     | FStar_Tactics_Result.Failed (e, ps') ->
                         FStar_Tactics_Result.Failed (e, ps'))))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (829)) (Prims.of_int (23))
                                (Prims.of_int (829)) (Prims.of_int (39))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (829)) (Prims.of_int (2))
                          (Prims.of_int (832)) (Prims.of_int (3))))))
let rec (visit_tm :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun ff ->
    fun t ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (835)) (Prims.of_int (11))
                               (Prims.of_int (835)) (Prims.of_int (23))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (836)) (Prims.of_int (2))
                         (Prims.of_int (888)) (Prims.of_int (18)))))
        with
        | true ->
            (match (match FStar_Reflection_Builtins.inspect_ln t with
                    | FStar_Reflection_Data.Tv_FVar uu___ ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Builtins.inspect_ln t), s))
                    | FStar_Reflection_Data.Tv_Var bv ->
                        (fun ps1 ->
                           match (on_sort_bv (visit_tm ff) bv)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (840))
                                               (Prims.of_int (17))
                                               (Prims.of_int (840))
                                               (Prims.of_int (44))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (841))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (841))
                                                 (Prims.of_int (17)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_Var a),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (841))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (841))
                                                    (Prims.of_int (17))))))))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_BVar bv ->
                        (fun ps1 ->
                           match (on_sort_bv (visit_tm ff) bv)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (844))
                                               (Prims.of_int (17))
                                               (Prims.of_int (844))
                                               (Prims.of_int (44))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (845))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (845))
                                                 (Prims.of_int (18)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_BVar a),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (845))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (845))
                                                    (Prims.of_int (18))))))))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Type () ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Type ()), s))
                    | FStar_Reflection_Data.Tv_Const c ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Const c), s))
                    | FStar_Reflection_Data.Tv_Uvar (i, u) ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Uvar (i, u)), s))
                    | FStar_Reflection_Data.Tv_Unknown ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             (FStar_Reflection_Data.Tv_Unknown, s))
                    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
                        (fun ps1 ->
                           match (on_sort_binder (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (852))
                                               (Prims.of_int (16))
                                               (Prims.of_int (852))
                                               (Prims.of_int (46))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (853))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (854))
                                                 (Prims.of_int (20)))))
                                with
                                | true ->
                                    (match (visit_comp ff c)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (853))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (854))
                                                               (Prims.of_int (20))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (853))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (853))
                                                         (Prims.of_int (31))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (854))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (854))
                                                           (Prims.of_int (20)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Arrow
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (854))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (854))
                                                              (Prims.of_int (20))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Abs (b, t1) ->
                        (fun ps1 ->
                           match (on_sort_binder (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (856))
                                               (Prims.of_int (16))
                                               (Prims.of_int (856))
                                               (Prims.of_int (46))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (857))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (858))
                                                 (Prims.of_int (18)))))
                                with
                                | true ->
                                    (match (visit_tm ff t1)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (857))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (858))
                                                               (Prims.of_int (18))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (857))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (857))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (858))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (858))
                                                           (Prims.of_int (18)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Abs
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (858))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (858))
                                                              (Prims.of_int (18))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
                        (fun ps1 ->
                           match (visit_tm ff l)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (860))
                                               (Prims.of_int (17))
                                               (Prims.of_int (860))
                                               (Prims.of_int (30))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (861))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (862))
                                                 (Prims.of_int (24)))))
                                with
                                | true ->
                                    (match (visit_tm ff r)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (861))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (862))
                                                               (Prims.of_int (24))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (861))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (861))
                                                         (Prims.of_int (30))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (862))
                                                           (Prims.of_int (9))
                                                           (Prims.of_int (862))
                                                           (Prims.of_int (24)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_App
                                                    (a, (a1, q))),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (862))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (862))
                                                              (Prims.of_int (24))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Refine (b, r) ->
                        (fun ps1 ->
                           match (on_sort_bv (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (864))
                                               (Prims.of_int (16))
                                               (Prims.of_int (864))
                                               (Prims.of_int (42))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (865))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (866))
                                                 (Prims.of_int (21)))))
                                with
                                | true ->
                                    (match (visit_tm ff r)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (865))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (866))
                                                               (Prims.of_int (21))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (865))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (865))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (866))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (866))
                                                           (Prims.of_int (21)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Refine
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (866))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (866))
                                                              (Prims.of_int (21))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Let (r, attrs, b, def, t1) ->
                        (fun ps1 ->
                           match (on_sort_bv (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (868))
                                               (Prims.of_int (16))
                                               (Prims.of_int (868))
                                               (Prims.of_int (42))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (869))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (871))
                                                 (Prims.of_int (30)))))
                                with
                                | true ->
                                    (match (visit_tm ff def)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (869))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (871))
                                                               (Prims.of_int (30))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (869))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (869))
                                                         (Prims.of_int (33))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (870))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (871))
                                                           (Prims.of_int (30)))))
                                          with
                                          | true ->
                                              (match (visit_tm ff t1)
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (870))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (871))
                                                                    (Prims.of_int (30))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Derived.fst"
                                                                   (Prims.of_int (870))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (870))
                                                                   (Prims.of_int (29))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a2, ps'2) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (871))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (871))
                                                                    (Prims.of_int (30)))))
                                                    with
                                                    | true ->
                                                        FStar_Tactics_Result.Success
                                                          ((FStar_Reflection_Data.Tv_Let
                                                              (r, attrs, a,
                                                                a1, a2)),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (871))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (871))
                                                                    (Prims.of_int (30))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e, ps'2) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e, ps'2)))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Match (sc, ret_opt, brs) ->
                        (fun ps1 ->
                           match (visit_tm ff sc)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (873))
                                               (Prims.of_int (17))
                                               (Prims.of_int (873))
                                               (Prims.of_int (31))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (874))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (879))
                                                 (Prims.of_int (31)))))
                                with
                                | true ->
                                    (match (FStar_Tactics_Util.map_opt
                                              (fun ret ->
                                                 match ret with
                                                 | (FStar_Pervasives.Inl t1,
                                                    tacopt) ->
                                                     (fun ps2 ->
                                                        match match (visit_tm
                                                                    ff t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (48))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (48)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives.Inl
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (48))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a1, ps'1) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (78)))))
                                                             with
                                                             | true ->
                                                                 (match 
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (78))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (78))))))
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (78)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1, a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (876))
                                                                    (Prims.of_int (78))))))))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1))
                                                 | (FStar_Pervasives.Inr c,
                                                    tacopt) ->
                                                     (fun ps2 ->
                                                        match match (visit_comp
                                                                    ff c)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (50))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (50)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives.Inr
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (50))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a1, ps'1) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (80)))))
                                                             with
                                                             | true ->
                                                                 (match 
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (80))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (80))))))
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (80)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1, a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (80))))))))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)))
                                              ret_opt)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (874))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (879))
                                                               (Prims.of_int (31))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (874))
                                                         (Prims.of_int (22))
                                                         (Prims.of_int (877))
                                                         (Prims.of_int (89))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (878))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (879))
                                                           (Prims.of_int (31)))))
                                          with
                                          | true ->
                                              (match (FStar_Tactics_Util.map
                                                        (visit_br ff) brs)
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (31))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Derived.fst"
                                                                   (Prims.of_int (878))
                                                                   (Prims.of_int (18))
                                                                   (Prims.of_int (878))
                                                                   (Prims.of_int (39))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a2, ps'2) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (31)))))
                                                    with
                                                    | true ->
                                                        FStar_Tactics_Result.Success
                                                          ((FStar_Reflection_Data.Tv_Match
                                                              (a, a1, a2)),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (31))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e, ps'2) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e, ps'2)))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_AscribedT (e, t1, topt) ->
                        (fun ps1 ->
                           match (visit_tm ff e)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (881))
                                               (Prims.of_int (16))
                                               (Prims.of_int (881))
                                               (Prims.of_int (29))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (882))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (883))
                                                 (Prims.of_int (29)))))
                                with
                                | true ->
                                    (match (visit_tm ff t1)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (882))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (883))
                                                               (Prims.of_int (29))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (882))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (882))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (883))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (883))
                                                           (Prims.of_int (29)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_AscribedT
                                                    (a, a1, topt)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (883))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (883))
                                                              (Prims.of_int (29))))))))
                                     | FStar_Tactics_Result.Failed (e1, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e1, ps'1)))
                           | FStar_Tactics_Result.Failed (e1, ps') ->
                               FStar_Tactics_Result.Failed (e1, ps'))
                    | FStar_Reflection_Data.Tv_AscribedC (e, c, topt) ->
                        (fun ps1 ->
                           match (visit_tm ff e)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (885))
                                               (Prims.of_int (16))
                                               (Prims.of_int (885))
                                               (Prims.of_int (29))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (886))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (886))
                                                 (Prims.of_int (29)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_AscribedC
                                          (a, c, topt)),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (886))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (886))
                                                    (Prims.of_int (29))))))))
                           | FStar_Tactics_Result.Failed (e1, ps') ->
                               FStar_Tactics_Result.Failed (e1, ps')))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (835))
                                             (Prims.of_int (11))
                                             (Prims.of_int (835))
                                             (Prims.of_int (23))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (836))
                                       (Prims.of_int (2))
                                       (Prims.of_int (888))
                                       (Prims.of_int (18))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (837)) (Prims.of_int (4))
                                 (Prims.of_int (886)) (Prims.of_int (29))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (888)) (Prims.of_int (2))
                                   (Prims.of_int (888)) (Prims.of_int (18)))))
                  with
                  | true ->
                      (ff (FStar_Reflection_Builtins.pack_ln a))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (888)) (Prims.of_int (2))
                                    (Prims.of_int (888)) (Prims.of_int (18)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
and (visit_br :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Data.branch ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Data.branch FStar_Tactics_Result.__result)
  =
  fun ff ->
    fun b ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (890)) (Prims.of_int (15))
                               (Prims.of_int (890)) (Prims.of_int (16))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (890)) (Prims.of_int (2))
                         (Prims.of_int (893)) (Prims.of_int (8)))))
        with
        | true ->
            ((match b with
              | (p, t) ->
                  (fun ps1 ->
                     match (visit_pat ff p)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (891))
                                         (Prims.of_int (10))
                                         (Prims.of_int (891))
                                         (Prims.of_int (24))))))
                     with
                     | FStar_Tactics_Result.Success (a, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (892))
                                           (Prims.of_int (2))
                                           (Prims.of_int (893))
                                           (Prims.of_int (8)))))
                          with
                          | true ->
                              (match (visit_tm ff t)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (892))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (893))
                                                         (Prims.of_int (8))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (892))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (892))
                                                   (Prims.of_int (23))))))
                               with
                               | FStar_Tactics_Result.Success (a1, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (893))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (893))
                                                     (Prims.of_int (8)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((a, a1),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (893))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (893))
                                                        (Prims.of_int (8))))))))
                               | FStar_Tactics_Result.Failed (e, ps'1) ->
                                   FStar_Tactics_Result.Failed (e, ps'1)))
                     | FStar_Tactics_Result.Failed (e, ps') ->
                         FStar_Tactics_Result.Failed (e, ps'))))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (890)) (Prims.of_int (15))
                                (Prims.of_int (890)) (Prims.of_int (16))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (890)) (Prims.of_int (2))
                          (Prims.of_int (893)) (Prims.of_int (8))))))
and (visit_pat :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Data.pattern ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Data.pattern FStar_Tactics_Result.__result)
  =
  fun ff ->
    fun p ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          (fun s -> FStar_Tactics_Result.Success (p, s))
      | FStar_Reflection_Data.Pat_Cons (fv, l) ->
          (fun ps ->
             match (FStar_Tactics_Util.map
                      (fun uu___ ->
                         match uu___ with
                         | (p1, b) ->
                             (fun ps1 ->
                                match (visit_pat ff p1)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (898))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (898))
                                                    (Prims.of_int (47))))))
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (898))
                                                      (Prims.of_int (32))
                                                      (Prims.of_int (898))
                                                      (Prims.of_int (51)))))
                                     with
                                     | true ->
                                         FStar_Tactics_Result.Success
                                           ((a, b),
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (898))
                                                         (Prims.of_int (32))
                                                         (Prims.of_int (898))
                                                         (Prims.of_int (51))))))))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps'))) l)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (898)) (Prims.of_int (14))
                                 (Prims.of_int (898)) (Prims.of_int (55))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (899)) (Prims.of_int (6))
                                   (Prims.of_int (899)) (Prims.of_int (19)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Data.Pat_Cons (fv, a)),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (899)) (Prims.of_int (6))
                                      (Prims.of_int (899))
                                      (Prims.of_int (19))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | FStar_Reflection_Data.Pat_Var bv ->
          (fun ps ->
             match (on_sort_bv (visit_tm ff) bv)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (901)) (Prims.of_int (15))
                                 (Prims.of_int (901)) (Prims.of_int (42))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (902)) (Prims.of_int (6))
                                   (Prims.of_int (902)) (Prims.of_int (16)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Data.Pat_Var a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (902)) (Prims.of_int (6))
                                      (Prims.of_int (902))
                                      (Prims.of_int (16))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | FStar_Reflection_Data.Pat_Wild bv ->
          (fun ps ->
             match (on_sort_bv (visit_tm ff) bv)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (904)) (Prims.of_int (15))
                                 (Prims.of_int (904)) (Prims.of_int (42))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (905)) (Prims.of_int (6))
                                   (Prims.of_int (905)) (Prims.of_int (17)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Data.Pat_Wild a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (905)) (Prims.of_int (6))
                                      (Prims.of_int (905))
                                      (Prims.of_int (17))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | FStar_Reflection_Data.Pat_Dot_Term (bv, term) ->
          (fun ps ->
             match (on_sort_bv (visit_tm ff) bv)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (907)) (Prims.of_int (15))
                                 (Prims.of_int (907)) (Prims.of_int (42))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (908)) (Prims.of_int (6))
                                   (Prims.of_int (909)) (Prims.of_int (26)))))
                  with
                  | true ->
                      (match (visit_tm ff term)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (908))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (909))
                                                 (Prims.of_int (26))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (908))
                                           (Prims.of_int (17))
                                           (Prims.of_int (908))
                                           (Prims.of_int (33))))))
                       with
                       | FStar_Tactics_Result.Success (a1, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (909))
                                             (Prims.of_int (6))
                                             (Prims.of_int (909))
                                             (Prims.of_int (26)))))
                            with
                            | true ->
                                FStar_Tactics_Result.Success
                                  ((FStar_Reflection_Data.Pat_Dot_Term
                                      (a, a1)),
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (909))
                                                (Prims.of_int (6))
                                                (Prims.of_int (909))
                                                (Prims.of_int (26))))))))
                       | FStar_Tactics_Result.Failed (e, ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
and (visit_comp :
  (FStar_Reflection_Types.term ->
     FStar_Tactics_Types.proofstate ->
       FStar_Reflection_Types.term FStar_Tactics_Result.__result)
    ->
    FStar_Reflection_Types.comp ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.comp FStar_Tactics_Result.__result)
  =
  fun ff ->
    fun c ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (911)) (Prims.of_int (11))
                               (Prims.of_int (911)) (Prims.of_int (25))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (912)) (Prims.of_int (2))
                         (Prims.of_int (935)) (Prims.of_int (15)))))
        with
        | true ->
            (match (match FStar_Reflection_Builtins.inspect_comp c with
                    | FStar_Reflection_Data.C_Total (ret, decr) ->
                        (fun ps1 ->
                           match (visit_tm ff ret)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (915))
                                               (Prims.of_int (18))
                                               (Prims.of_int (915))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (916))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (917))
                                                 (Prims.of_int (24)))))
                                with
                                | true ->
                                    (match (FStar_Tactics_Util.map
                                              (visit_tm ff) decr)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (916))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (917))
                                                               (Prims.of_int (24))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (916))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (916))
                                                         (Prims.of_int (41))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (917))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (917))
                                                           (Prims.of_int (24)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.C_Total
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (917))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (917))
                                                              (Prims.of_int (24))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.C_GTotal (ret, decr) ->
                        (fun ps1 ->
                           match (visit_tm ff ret)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (920))
                                               (Prims.of_int (18))
                                               (Prims.of_int (920))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (921))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (922))
                                                 (Prims.of_int (25)))))
                                with
                                | true ->
                                    (match (FStar_Tactics_Util.map
                                              (visit_tm ff) decr)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (921))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (922))
                                                               (Prims.of_int (25))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (921))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (921))
                                                         (Prims.of_int (41))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (922))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (922))
                                                           (Prims.of_int (25)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.C_GTotal
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (922))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (922))
                                                              (Prims.of_int (25))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
                        (fun ps1 ->
                           match (visit_tm ff pre)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (925))
                                               (Prims.of_int (18))
                                               (Prims.of_int (925))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (926))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (928))
                                                 (Prims.of_int (29)))))
                                with
                                | true ->
                                    (match (visit_tm ff post)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (926))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (928))
                                                               (Prims.of_int (29))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (926))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (926))
                                                         (Prims.of_int (35))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (927))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (928))
                                                           (Prims.of_int (29)))))
                                          with
                                          | true ->
                                              (match (visit_tm ff pats)
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (927))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (29))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Derived.fst"
                                                                   (Prims.of_int (927))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (927))
                                                                   (Prims.of_int (35))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a2, ps'2) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (29)))))
                                                    with
                                                    | true ->
                                                        FStar_Tactics_Result.Success
                                                          ((FStar_Reflection_Data.C_Lemma
                                                              (a, a1, a2)),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (29))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e, ps'2) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e, ps'2)))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
                        (fun ps1 ->
                           match (visit_tm ff res)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (931))
                                               (Prims.of_int (18))
                                               (Prims.of_int (931))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (932))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (933))
                                                 (Prims.of_int (29)))))
                                with
                                | true ->
                                    (match (FStar_Tactics_Util.map
                                              (fun uu___ ->
                                                 match uu___ with
                                                 | (a1, q) ->
                                                     (fun ps2 ->
                                                        match (visit_tm ff a1)
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (52))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a2, ps'1) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (56)))))
                                                             with
                                                             | true ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((a2, q),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (56))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)))
                                              args)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (932))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (933))
                                                               (Prims.of_int (29))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (932))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (932))
                                                         (Prims.of_int (62))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a1, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (933))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (933))
                                                           (Prims.of_int (29)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.C_Eff
                                                    (us, eff, a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (933))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (933))
                                                              (Prims.of_int (29))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps')))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (911))
                                             (Prims.of_int (11))
                                             (Prims.of_int (911))
                                             (Prims.of_int (25))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (912))
                                       (Prims.of_int (2))
                                       (Prims.of_int (935))
                                       (Prims.of_int (15))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (913)) (Prims.of_int (4))
                                 (Prims.of_int (933)) (Prims.of_int (29))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (935)) (Prims.of_int (2))
                                   (Prims.of_int (935)) (Prims.of_int (15)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Builtins.pack_comp a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (935)) (Prims.of_int (2))
                                      (Prims.of_int (935))
                                      (Prims.of_int (15))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec (destruct_list :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term Prims.list FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (938)) (Prims.of_int (21))
                             (Prims.of_int (938)) (Prims.of_int (34))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Derived.fst"
                       (Prims.of_int (938)) (Prims.of_int (4))
                       (Prims.of_int (950)) (Prims.of_int (27)))))
      with
      | true ->
          ((match FStar_Reflection_Derived.collect_app t with
            | (head, args) ->
                (match ((FStar_Reflection_Builtins.inspect_ln head), args)
                 with
                 | (FStar_Reflection_Data.Tv_FVar fv,
                    (a1, FStar_Reflection_Data.Q_Explicit)::(a2,
                                                             FStar_Reflection_Data.Q_Explicit)::[])
                     ->
                     if
                       (FStar_Reflection_Builtins.inspect_fv fv) =
                         FStar_Reflection_Const.cons_qn
                     then
                       (fun ps1 ->
                          match (destruct_list a2)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (943))
                                              (Prims.of_int (17))
                                              (Prims.of_int (943))
                                              (Prims.of_int (33))))))
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (943))
                                                (Prims.of_int (14))
                                                (Prims.of_int (943))
                                                (Prims.of_int (16)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((a1 :: a),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (943))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (943))
                                                   (Prims.of_int (16))))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps'))
                     else
                       FStar_Tactics_Effect.raise
                         FStar_Tactics_Common.NotAListLiteral
                 | (FStar_Reflection_Data.Tv_FVar fv,
                    (uu___, FStar_Reflection_Data.Q_Implicit)::(a1,
                                                                FStar_Reflection_Data.Q_Explicit)::
                    (a2, FStar_Reflection_Data.Q_Explicit)::[]) ->
                     if
                       (FStar_Reflection_Builtins.inspect_fv fv) =
                         FStar_Reflection_Const.cons_qn
                     then
                       (fun ps1 ->
                          match (destruct_list a2)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (943))
                                              (Prims.of_int (17))
                                              (Prims.of_int (943))
                                              (Prims.of_int (33))))))
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (943))
                                                (Prims.of_int (14))
                                                (Prims.of_int (943))
                                                (Prims.of_int (16)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((a1 :: a),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (943))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (943))
                                                   (Prims.of_int (16))))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps'))
                     else
                       FStar_Tactics_Effect.raise
                         FStar_Tactics_Common.NotAListLiteral
                 | (FStar_Reflection_Data.Tv_FVar fv, uu___) ->
                     if
                       (FStar_Reflection_Builtins.inspect_fv fv) =
                         FStar_Reflection_Const.nil_qn
                     then (fun s -> FStar_Tactics_Result.Success ([], s))
                     else
                       FStar_Tactics_Effect.raise
                         FStar_Tactics_Common.NotAListLiteral
                 | uu___ ->
                     FStar_Tactics_Effect.raise
                       FStar_Tactics_Common.NotAListLiteral)))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (938)) (Prims.of_int (21))
                              (Prims.of_int (938)) (Prims.of_int (34))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (938)) (Prims.of_int (4))
                        (Prims.of_int (950)) (Prims.of_int (27))))))
let (get_match_body :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (cur_goal ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (953)) (Prims.of_int (8))
                                      (Prims.of_int (953))
                                      (Prims.of_int (55))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (953)) (Prims.of_int (42))
                                (Prims.of_int (953)) (Prims.of_int (55))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (953)) (Prims.of_int (8))
                                  (Prims.of_int (953)) (Prims.of_int (55)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((FStar_Reflection_Formula.unsquash a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (953)) (Prims.of_int (8))
                                     (Prims.of_int (953)) (Prims.of_int (55))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (953)) (Prims.of_int (2))
                            (Prims.of_int (957)) (Prims.of_int (46)))))
           with
           | true ->
               ((match a with
                 | FStar_Pervasives_Native.None -> fail ""
                 | FStar_Pervasives_Native.Some t ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.inspect t)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (955))
                                            (Prims.of_int (20))
                                            (Prims.of_int (955))
                                            (Prims.of_int (29))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (955))
                                              (Prims.of_int (14))
                                              (Prims.of_int (957))
                                              (Prims.of_int (46)))))
                             with
                             | true ->
                                 ((match a1 with
                                   | FStar_Reflection_Data.Tv_Match
                                       (sc, uu___1, uu___2) ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success
                                            (sc, s))
                                   | uu___1 -> fail "Goal is not a match"))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (955))
                                               (Prims.of_int (14))
                                               (Prims.of_int (957))
                                               (Prims.of_int (46)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (953)) (Prims.of_int (2))
                             (Prims.of_int (957)) (Prims.of_int (46)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec last :
  'a .
    'a Prims.list ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun x ->
    match x with
    | [] -> fail "last: empty list"
    | x1::[] -> (fun s -> FStar_Tactics_Result.Success (x1, s))
    | uu___::xs -> last xs
let (branch_on_match :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    focus
      (fun uu___1 ->
         fun ps ->
           match (get_match_body ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (970)) (Prims.of_int (14))
                               (Prims.of_int (970)) (Prims.of_int (31))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (971)) (Prims.of_int (6))
                                 (Prims.of_int (976)) (Prims.of_int (20)))))
                with
                | true ->
                    (match (FStar_Tactics_Builtins.t_destruct a)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (971))
                                               (Prims.of_int (6))
                                               (Prims.of_int (976))
                                               (Prims.of_int (20))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (971))
                                         (Prims.of_int (14))
                                         (Prims.of_int (971))
                                         (Prims.of_int (26))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (972))
                                           (Prims.of_int (6))
                                           (Prims.of_int (976))
                                           (Prims.of_int (20)))))
                          with
                          | true ->
                              (iterAll
                                 (fun uu___2 ->
                                    fun ps1 ->
                                      match (repeat
                                               FStar_Tactics_Builtins.intro)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (973))
                                                          (Prims.of_int (17))
                                                          (Prims.of_int (973))
                                                          (Prims.of_int (29))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (974))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (976))
                                                            (Prims.of_int (19)))))
                                           with
                                           | true ->
                                               (match (last a2)
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (974))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (19))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (974))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (974))
                                                                    (Prims.of_int (23))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a3, ps'3) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'3
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (975))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (19)))))
                                                     with
                                                     | true ->
                                                         (match (grewrite_eq
                                                                   a3)
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (975))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (975))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (975))
                                                                    (Prims.of_int (21))))))
                                                          with
                                                          | FStar_Tactics_Result.Success
                                                              (a4, ps'4) ->
                                                              (match 
                                                                 FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (19)))))
                                                               with
                                                               | true ->
                                                                   (FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.iota])
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (976))
                                                                    (Prims.of_int (19)))))))
                                                          | FStar_Tactics_Result.Failed
                                                              (e, ps'4) ->
                                                              FStar_Tactics_Result.Failed
                                                                (e, ps'4)))
                                                | FStar_Tactics_Result.Failed
                                                    (e, ps'3) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'3)))
                                      | FStar_Tactics_Result.Failed (e, ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (972))
                                            (Prims.of_int (6))
                                            (Prims.of_int (976))
                                            (Prims.of_int (20)))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (nth_binder :
  Prims.int ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun i ->
    fun ps ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (985)) (Prims.of_int (11))
                          (Prims.of_int (985)) (Prims.of_int (25))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (986)) (Prims.of_int (2))
                            (Prims.of_int (990)) (Prims.of_int (15)))))
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
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (986))
                                             (Prims.of_int (2))
                                             (Prims.of_int (990))
                                             (Prims.of_int (15))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (986))
                                       (Prims.of_int (16))
                                       (Prims.of_int (986))
                                       (Prims.of_int (65))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (987)) (Prims.of_int (2))
                                 (Prims.of_int (990)) (Prims.of_int (15)))))
                with
                | true ->
                    (match (if
                              (if i >= Prims.int_zero
                               then i
                               else (FStar_List_Tot_Base.length a) + i) <
                                Prims.int_zero
                            then fail "not enough binders"
                            else
                              (fun s ->
                                 FStar_Tactics_Result.Success
                                   ((if i >= Prims.int_zero
                                     then i
                                     else (FStar_List_Tot_Base.length a) + i),
                                     s)))
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
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (986))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (990))
                                                           (Prims.of_int (15))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (986))
                                                     (Prims.of_int (16))
                                                     (Prims.of_int (986))
                                                     (Prims.of_int (65))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (987))
                                               (Prims.of_int (2))
                                               (Prims.of_int (990))
                                               (Prims.of_int (15))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (987))
                                         (Prims.of_int (16))
                                         (Prims.of_int (987))
                                         (Prims.of_int (62))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (988))
                                           (Prims.of_int (2))
                                           (Prims.of_int (990))
                                           (Prims.of_int (15)))))
                          with
                          | true ->
                              ((match FStar_List_Tot_Base.nth a a1 with
                                | FStar_Pervasives_Native.None ->
                                    fail "not enough binders"
                                | FStar_Pervasives_Native.Some b ->
                                    (fun s ->
                                       FStar_Tactics_Result.Success (b, s))))
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (988))
                                            (Prims.of_int (2))
                                            (Prims.of_int (990))
                                            (Prims.of_int (15)))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
exception Appears 
let (uu___is_Appears : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Appears -> true | uu___ -> false
let (name_appears_in :
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        Prims.bool FStar_Tactics_Result.__result)
  =
  fun nm ->
    fun t ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (998)) (Prims.of_int (4))
                               (Prims.of_int (1003)) (Prims.of_int (12))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.Derived.fst"
                         (Prims.of_int (1005)) (Prims.of_int (2))
                         (Prims.of_int (1007)) (Prims.of_int (16)))))
        with
        | true ->
            (try_with
               (fun uu___ ->
                  match () with
                  | () ->
                      (fun ps1 ->
                         match match (visit_tm
                                        (fun t1 ->
                                           fun ps2 ->
                                             match (FStar_Tactics_Builtins.inspect
                                                      t1)
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Derived.fst"
                                                                 (Prims.of_int (997))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (997))
                                                                 (Prims.of_int (11))))))
                                             with
                                             | FStar_Tactics_Result.Success
                                                 (a, ps') ->
                                                 (match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Derived.fst"
                                                                   (Prims.of_int (997))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (997))
                                                                   (Prims.of_int (11)))))
                                                  with
                                                  | true ->
                                                      ((match a with
                                                        | FStar_Reflection_Data.Tv_FVar
                                                            fv ->
                                                            (fun ps3 ->
                                                               match 
                                                                 (if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv) = nm
                                                                  then
                                                                    FStar_Tactics_Effect.raise
                                                                    Appears
                                                                  else
                                                                    (
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((), s)))
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (1000))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1001))
                                                                    (Prims.of_int (21))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (11)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (t1,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (11))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e, ps'1)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'1))
                                                        | t2 ->
                                                            FStar_Tactics_Builtins.pack
                                                              t2))
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (997))
                                                                    (Prims.of_int (11)))))))
                                             | FStar_Tactics_Result.Failed
                                                 (e, ps') ->
                                                 FStar_Tactics_Result.Failed
                                                   (e, ps')) t)
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (1005))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (1005))
                                                         (Prims.of_int (28))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (1005))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (1005))
                                                   (Prims.of_int (28))))))
                               with
                               | FStar_Tactics_Result.Success (a, ps') ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (1005))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (1005))
                                                     (Prims.of_int (28)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (1005))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (1005))
                                                        (Prims.of_int (28))))))))
                               | FStar_Tactics_Result.Failed (e, ps') ->
                                   FStar_Tactics_Result.Failed (e, ps')
                         with
                         | FStar_Tactics_Result.Success (a, ps') ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (1005))
                                               (Prims.of_int (30))
                                               (Prims.of_int (1005))
                                               (Prims.of_int (35)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    (false,
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (1005))
                                                  (Prims.of_int (30))
                                                  (Prims.of_int (1005))
                                                  (Prims.of_int (35))))))))
                         | FStar_Tactics_Result.Failed (e, ps') ->
                             FStar_Tactics_Result.Failed (e, ps')))
               (fun uu___ ->
                  match uu___ with
                  | Appears ->
                      (fun s -> FStar_Tactics_Result.Success (true, s))
                  | e -> FStar_Tactics_Effect.raise e))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (998)) (Prims.of_int (4))
                                (Prims.of_int (1003)) (Prims.of_int (12))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (1005)) (Prims.of_int (2))
                          (Prims.of_int (1007)) (Prims.of_int (16))))))
let rec (mk_abs :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun args ->
    fun t ->
      match args with
      | [] -> (fun s -> FStar_Tactics_Result.Success (t, s))
      | a::args' ->
          (fun ps ->
             match (mk_abs args' t)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (1014)) (Prims.of_int (13))
                                 (Prims.of_int (1014)) (Prims.of_int (27))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (1015)) (Prims.of_int (4))
                                   (Prims.of_int (1015)) (Prims.of_int (22)))))
                  with
                  | true ->
                      (FStar_Tactics_Builtins.pack
                         (FStar_Reflection_Data.Tv_Abs (a, a1)))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (1015)) (Prims.of_int (4))
                                    (Prims.of_int (1015)) (Prims.of_int (22)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))