open Prims
let (fetch_eq_side :
  unit ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.term * FStar_Reflection_Types.term)
        FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (63)) (Prims.of_int (10))
                          (Prims.of_int (63)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (64)) (Prims.of_int (2))
                            (Prims.of_int (86)) (Prims.of_int (39)))))
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
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (64))
                                          (Prims.of_int (2))
                                          (Prims.of_int (86))
                                          (Prims.of_int (39))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (64)) (Prims.of_int (8))
                                    (Prims.of_int (64)) (Prims.of_int (17))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (64)) (Prims.of_int (2))
                                      (Prims.of_int (86)) (Prims.of_int (39)))))
                     with
                     | true ->
                         ((match a1 with
                           | FStar_Reflection_Data.Tv_App
                               (squash, (g, uu___1)) ->
                               (fun ps1 ->
                                  match (FStar_Tactics_Builtins.inspect
                                           squash)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (66))
                                                      (Prims.of_int (11))
                                                      (Prims.of_int (66))
                                                      (Prims.of_int (25))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (66))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (85))
                                                        (Prims.of_int (51)))))
                                       with
                                       | true ->
                                           ((match a2 with
                                             | FStar_Reflection_Data.Tv_FVar
                                                 squash1 ->
                                                 if
                                                   (FStar_Reflection_Derived.fv_to_string
                                                      squash1)
                                                     =
                                                     (FStar_Reflection_Derived.flatten_name
                                                        FStar_Reflection_Const.squash_qn)
                                                 then
                                                   (fun ps2 ->
                                                      match (FStar_Tactics_Builtins.inspect
                                                               g)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (25))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a3, ps'3) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (48)))))
                                                           with
                                                           | true ->
                                                               ((match a3
                                                                 with
                                                                 | FStar_Reflection_Data.Tv_App
                                                                    (eq_type_x,
                                                                    (y,
                                                                    uu___2))
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type_x)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (36))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_App
                                                                    (eq_type,
                                                                    (x,
                                                                    uu___3))
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (37))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_App
                                                                    (eq,
                                                                    (typ,
                                                                    uu___4))
                                                                    ->
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (35))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (55)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a6
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    eq1 ->
                                                                    if
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((x, y),
                                                                    s))
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an equality"
                                                                    | uu___5
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app2 of fvar: "))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (55)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6))
                                                                    | uu___4
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app3"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (42)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                    | uu___3
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app2"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (39)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                 | uu___2 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app under squash"))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (48)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps'3) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'3))
                                                 else
                                                   FStar_Tactics_Derived.fail
                                                     "not a squash"
                                             | uu___2 ->
                                                 FStar_Tactics_Derived.fail
                                                   "not an app of fvar at top level"))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (66))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (85))
                                                         (Prims.of_int (51)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))
                           | uu___1 ->
                               FStar_Tactics_Derived.fail
                                 "not an app at top level"))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (64)) (Prims.of_int (2))
                                       (Prims.of_int (86))
                                       (Prims.of_int (39)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let mustfail :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      Prims.string ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun t ->
    fun message ->
      fun ps ->
        match (FStar_Tactics_Derived.trytac t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (132)) (Prims.of_int (10))
                            (Prims.of_int (132)) (Prims.of_int (18))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (132)) (Prims.of_int (4))
                              (Prims.of_int (134)) (Prims.of_int (16)))))
             with
             | true ->
                 ((match a1 with
                   | FStar_Pervasives_Native.Some uu___ ->
                       FStar_Tactics_Derived.fail message
                   | FStar_Pervasives_Native.None ->
                       (fun s -> FStar_Tactics_Result.Success ((), s))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (132)) (Prims.of_int (4))
                               (Prims.of_int (134)) (Prims.of_int (16)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (implies_intro' :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Logic.implies_intro ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (140)) (Prims.of_int (10))
                          (Prims.of_int (140)) (Prims.of_int (26))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (140)) (Prims.of_int (30))
                            (Prims.of_int (140)) (Prims.of_int (32)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (140)) (Prims.of_int (30))
                               (Prims.of_int (140)) (Prims.of_int (32))))))))
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
      match (FStar_Tactics_Derived.repeat f)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (143)) (Prims.of_int (10))
                          (Prims.of_int (143)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (143)) (Prims.of_int (22))
                            (Prims.of_int (143)) (Prims.of_int (24)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (143)) (Prims.of_int (22))
                               (Prims.of_int (143)) (Prims.of_int (24))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (and_elim' :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun h ->
    fun ps ->
      match match (FStar_Tactics_Builtins.pack
                     (FStar_Reflection_Data.Tv_Var
                        (FStar_Reflection_Derived.bv_of_binder h)))
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (146)) (Prims.of_int (2))
                                      (Prims.of_int (146))
                                      (Prims.of_int (43))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (146)) (Prims.of_int (11))
                                (Prims.of_int (146)) (Prims.of_int (43))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (146)) (Prims.of_int (2))
                                  (Prims.of_int (146)) (Prims.of_int (43)))))
                 with
                 | true ->
                     (FStar_Tactics_Logic.and_elim a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (146)) (Prims.of_int (2))
                                   (Prims.of_int (146)) (Prims.of_int (43)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (147)) (Prims.of_int (2))
                            (Prims.of_int (147)) (Prims.of_int (9)))))
           with
           | true ->
               (FStar_Tactics_Builtins.clear h)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (147)) (Prims.of_int (2))
                             (Prims.of_int (147)) (Prims.of_int (9)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let exact_hyp :
  'a .
    FStar_Reflection_Types.binder ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun h ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (151)) (Prims.of_int (11))
                             (Prims.of_int (151)) (Prims.of_int (48))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                       (Prims.of_int (152)) (Prims.of_int (2))
                       (Prims.of_int (152)) (Prims.of_int (68)))))
      with
      | true ->
          (match match match match (FStar_Tactics_Builtins.pack
                                      (FStar_Reflection_Data.Tv_Var
                                         (FStar_Reflection_Derived.bv_of_binder
                                            h)))
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
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
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (48))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (68))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (152))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (152))
                                                                   (Prims.of_int (68))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (152))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (152))
                                                             (Prims.of_int (67))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (152))
                                                       (Prims.of_int (20))
                                                       (Prims.of_int (152))
                                                       (Prims.of_int (66))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (152))
                                                 (Prims.of_int (21))
                                                 (Prims.of_int (152))
                                                 (Prims.of_int (53))))))
                             with
                             | FStar_Tactics_Result.Success (a1, ps') ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (152))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (152))
                                                   (Prims.of_int (66)))))
                                  with
                                  | true ->
                                      FStar_Tactics_Result.Success
                                        ((a1,
                                           FStar_Reflection_Data.Q_Explicit),
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (152))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (152))
                                                      (Prims.of_int (66))))))))
                             | FStar_Tactics_Result.Failed (e, ps') ->
                                 FStar_Tactics_Result.Failed (e, ps')
                       with
                       | FStar_Tactics_Result.Success (a1, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (152))
                                             (Prims.of_int (19))
                                             (Prims.of_int (152))
                                             (Prims.of_int (67)))))
                            with
                            | true ->
                                FStar_Tactics_Result.Success
                                  ([a1],
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (152))
                                                (Prims.of_int (19))
                                                (Prims.of_int (152))
                                                (Prims.of_int (67))))))))
                       | FStar_Tactics_Result.Failed (e, ps') ->
                           FStar_Tactics_Result.Failed (e, ps')
                 with
                 | FStar_Tactics_Result.Success (a1, ps') ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (152))
                                       (Prims.of_int (8))
                                       (Prims.of_int (152))
                                       (Prims.of_int (68)))))
                      with
                      | true ->
                          FStar_Tactics_Result.Success
                            ((FStar_Reflection_Derived.mk_app
                                (Obj.magic
                                   (failwith
                                      "Cannot evaluate open quotation at runtime"))
                                a1),
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (152))
                                          (Prims.of_int (8))
                                          (Prims.of_int (152))
                                          (Prims.of_int (68))))))))
                 | FStar_Tactics_Result.Failed (e, ps') ->
                     FStar_Tactics_Result.Failed (e, ps')
           with
           | FStar_Tactics_Result.Success (a1, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (152)) (Prims.of_int (2))
                                 (Prims.of_int (152)) (Prims.of_int (68)))))
                with
                | true ->
                    (FStar_Tactics_Derived.exact a1)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (152)) (Prims.of_int (2))
                                  (Prims.of_int (152)) (Prims.of_int (68)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (exact_hyp' :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun h ->
    fun ps ->
      match (FStar_Tactics_Builtins.pack
               (FStar_Reflection_Data.Tv_Var
                  (FStar_Reflection_Derived.bv_of_binder h)))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (156)) (Prims.of_int (8))
                          (Prims.of_int (156)) (Prims.of_int (40))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (156)) (Prims.of_int (2))
                            (Prims.of_int (156)) (Prims.of_int (40)))))
           with
           | true ->
               (FStar_Tactics_Derived.exact a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (156)) (Prims.of_int (2))
                             (Prims.of_int (156)) (Prims.of_int (40)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
type varname = Prims.string
type qn = Prims.string
type pattern =
  | PAny 
  | PVar of varname 
  | PQn of qn 
  | PType 
  | PApp of pattern * pattern 
let (uu___is_PAny : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PAny -> true | uu___ -> false
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PVar name -> true | uu___ -> false
let (__proj__PVar__item__name : pattern -> varname) =
  fun projectee -> match projectee with | PVar name -> name
let (uu___is_PQn : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PQn qn1 -> true | uu___ -> false
let (__proj__PQn__item__qn : pattern -> qn) =
  fun projectee -> match projectee with | PQn qn1 -> qn1
let (uu___is_PType : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PType -> true | uu___ -> false
let (uu___is_PApp : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PApp (hd, arg) -> true | uu___ -> false
let (__proj__PApp__item__hd : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> hd
let (__proj__PApp__item__arg : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> arg
let (desc_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PAny -> "anything"
    | PVar uu___1 -> "a variable"
    | PQn qn1 -> Prims.strcat "a constant (" (Prims.strcat qn1 ")")
    | PType -> "Type"
    | PApp (uu___1, uu___2) -> "a function application"
let rec (string_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PAny -> "__"
    | PVar x -> Prims.strcat "?" x
    | PQn qn1 -> qn1
    | PType -> "Type"
    | PApp (l, r) ->
        Prims.strcat "("
          (Prims.strcat (string_of_pattern l)
             (Prims.strcat " " (Prims.strcat (string_of_pattern r) ")")))
type match_exception =
  | NameMismatch of (qn * qn) 
  | SimpleMismatch of (pattern * FStar_Reflection_Types.term) 
  | NonLinearMismatch of (varname * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term) 
  | UnsupportedTermInPattern of FStar_Reflection_Types.term 
  | IncorrectTypeInAbsPatBinder of FStar_Reflection_Types.typ 
let (uu___is_NameMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NameMismatch _0 -> true | uu___ -> false
let (__proj__NameMismatch__item___0 : match_exception -> (qn * qn)) =
  fun projectee -> match projectee with | NameMismatch _0 -> _0
let (uu___is_SimpleMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleMismatch _0 -> true | uu___ -> false
let (__proj__SimpleMismatch__item___0 :
  match_exception -> (pattern * FStar_Reflection_Types.term)) =
  fun projectee -> match projectee with | SimpleMismatch _0 -> _0
let (uu___is_NonLinearMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NonLinearMismatch _0 -> true | uu___ -> false
let (__proj__NonLinearMismatch__item___0 :
  match_exception ->
    (varname * FStar_Reflection_Types.term * FStar_Reflection_Types.term))
  = fun projectee -> match projectee with | NonLinearMismatch _0 -> _0
let (uu___is_UnsupportedTermInPattern : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnsupportedTermInPattern _0 -> true
    | uu___ -> false
let (__proj__UnsupportedTermInPattern__item___0 :
  match_exception -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | UnsupportedTermInPattern _0 -> _0
let (uu___is_IncorrectTypeInAbsPatBinder : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | IncorrectTypeInAbsPatBinder _0 -> true
    | uu___ -> false
let (__proj__IncorrectTypeInAbsPatBinder__item___0 :
  match_exception -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | IncorrectTypeInAbsPatBinder _0 -> _0
let (term_head :
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
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (208)) (Prims.of_int (8))
                          (Prims.of_int (208)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (208)) (Prims.of_int (2))
                            (Prims.of_int (223)) (Prims.of_int (30)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_Var bv ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Var", s))
                 | FStar_Reflection_Data.Tv_BVar fv ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_BVar", s))
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_FVar", s))
                 | FStar_Reflection_Data.Tv_App (f, x) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_App", s))
                 | FStar_Reflection_Data.Tv_Abs (x, t1) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Abs", s))
                 | FStar_Reflection_Data.Tv_Arrow (x, t1) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Arrow", s))
                 | FStar_Reflection_Data.Tv_Type () ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Type", s))
                 | FStar_Reflection_Data.Tv_Refine (x, t1) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Refine", s))
                 | FStar_Reflection_Data.Tv_Const cst ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Const", s))
                 | FStar_Reflection_Data.Tv_Uvar (i, t1) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Uvar", s))
                 | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Let", s))
                 | FStar_Reflection_Data.Tv_Match (t1, uu___, branches) ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Match", s))
                 | FStar_Reflection_Data.Tv_AscribedT (uu___, uu___1, uu___2)
                     ->
                     (fun s ->
                        FStar_Tactics_Result.Success ("Tv_AscribedT", s))
                 | FStar_Reflection_Data.Tv_AscribedC (uu___, uu___1, uu___2)
                     ->
                     (fun s ->
                        FStar_Tactics_Result.Success ("Tv_AscribedC", s))
                 | FStar_Reflection_Data.Tv_Unknown ->
                     (fun s -> FStar_Tactics_Result.Success ("Tv_Unknown", s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (208)) (Prims.of_int (2))
                             (Prims.of_int (223)) (Prims.of_int (30)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (string_of_match_exception :
  match_exception ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    match uu___ with
    | NameMismatch (qn1, qn2) ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((Prims.strcat "Match failure (name mismatch): expecting "
                 (Prims.strcat qn1 (Prims.strcat ", found " qn2))), s))
    | SimpleMismatch (pat, tm) ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((Prims.strcat "Match failure (sort mismatch): expecting "
                 (Prims.strcat (desc_of_pattern pat)
                    (Prims.strcat ", got "
                       (FStar_Reflection_Builtins.term_to_string tm)))), s))
    | NonLinearMismatch (nm, t1, t2) ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((Prims.strcat "Match failure (nonlinear mismatch): variable "
                 (Prims.strcat nm
                    (Prims.strcat " needs to match both "
                       (Prims.strcat
                          (FStar_Reflection_Builtins.term_to_string t1)
                          (Prims.strcat " and "
                             (FStar_Reflection_Builtins.term_to_string t2)))))),
               s))
    | UnsupportedTermInPattern tm ->
        (fun ps ->
           match match match match (term_head tm)
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
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (238))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (238))
                                                                   (Prims.of_int (49))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (238))
                                                             (Prims.of_int (24))
                                                             (Prims.of_int (238))
                                                             (Prims.of_int (49))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (238))
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (238))
                                                       (Prims.of_int (49))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (238))
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (238))
                                                 (Prims.of_int (43))))))
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
                                        ((Prims.strcat a ")"),
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
                                  ((Prims.strcat " (" a),
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
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (603))
                                       (Prims.of_int (19))
                                       (Prims.of_int (603))
                                       (Prims.of_int (31)))))
                      with
                      | true ->
                          FStar_Tactics_Result.Success
                            ((Prims.strcat
                                (FStar_Reflection_Builtins.term_to_string tm)
                                a),
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
                              (Prims.mk_range "prims.fst"
                                 (Prims.of_int (603)) (Prims.of_int (19))
                                 (Prims.of_int (603)) (Prims.of_int (31)))))
                with
                | true ->
                    FStar_Tactics_Result.Success
                      ((Prims.strcat
                          "Match failure (unsupported term in pattern): " a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | IncorrectTypeInAbsPatBinder typ ->
        (fun s ->
           FStar_Tactics_Result.Success
             ((Prims.strcat "Incorrect type in pattern-matching binder: "
                 (Prims.strcat (FStar_Reflection_Builtins.term_to_string typ)
                    " (use one of ``var``, ``hyp \226\128\166``, or ``goal \226\128\166``)")),
               s))
type 'a match_res =
  | Success of 'a 
  | Failure of match_exception 
let uu___is_Success : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 : 'a . 'a match_res -> 'a =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Failure : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Failure _0 -> true | uu___ -> false
let __proj__Failure__item___0 : 'a . 'a match_res -> match_exception =
  fun projectee -> match projectee with | Failure _0 -> _0
let return : 'a . 'a -> 'a match_res = fun x -> Success x
let bind :
  'a 'b .
    'a match_res ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           'b match_res FStar_Tactics_Result.__result)
        ->
        FStar_Tactics_Types.proofstate ->
          'b match_res FStar_Tactics_Result.__result
  =
  fun f ->
    fun g ->
      match f with
      | Success aa -> g aa
      | Failure ex ->
          (fun s -> FStar_Tactics_Result.Success ((Failure ex), s))
let raise : 'a . match_exception -> 'a match_res = fun ex -> Failure ex
let lift_exn_tac :
  'a 'b .
    ('a -> 'b match_res) ->
      'a ->
        FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun f ->
    fun aa ->
      match f aa with
      | Success bb -> (fun s -> FStar_Tactics_Result.Success (bb, s))
      | Failure ex ->
          (fun ps ->
             match (string_of_match_exception ex)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (272)) (Prims.of_int (31))
                                 (Prims.of_int (272)) (Prims.of_int (61))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (272)) (Prims.of_int (18))
                                   (Prims.of_int (272)) (Prims.of_int (61)))))
                  with
                  | true ->
                      (FStar_Tactics_Derived.fail a1)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (272)) (Prims.of_int (18))
                                    (Prims.of_int (272)) (Prims.of_int (61)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let lift_exn_tactic :
  'a 'b .
    ('a -> 'b match_res) ->
      'a ->
        FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun f ->
    fun aa ->
      match f aa with
      | Success bb -> (fun s -> FStar_Tactics_Result.Success (bb, s))
      | Failure ex ->
          (fun ps ->
             match (string_of_match_exception ex)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (277)) (Prims.of_int (31))
                                 (Prims.of_int (277)) (Prims.of_int (61))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (277)) (Prims.of_int (18))
                                   (Prims.of_int (277)) (Prims.of_int (61)))))
                  with
                  | true ->
                      (FStar_Tactics_Derived.fail a1)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (277)) (Prims.of_int (18))
                                    (Prims.of_int (277)) (Prims.of_int (61)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
type bindings = (varname * FStar_Reflection_Types.term) Prims.list
let (string_of_bindings :
  bindings ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun bindings1 ->
    fun ps ->
      match (FStar_Tactics_Util.map
               (fun uu___ ->
                  fun s ->
                    FStar_Tactics_Result.Success
                      ((match uu___ with
                        | (nm, tm) ->
                            Prims.strcat ">> "
                              (Prims.strcat nm
                                 (Prims.strcat ": "
                                    (FStar_Reflection_Builtins.term_to_string
                                       tm)))), s)) bindings1)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (289)) (Prims.of_int (4))
                          (Prims.of_int (290)) (Prims.of_int (27))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (288)) (Prims.of_int (2))
                            (Prims.of_int (290)) (Prims.of_int (27)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_String.concat "\n" a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (288)) (Prims.of_int (2))
                               (Prims.of_int (290)) (Prims.of_int (27))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (interp_pattern_aux :
  pattern ->
    bindings ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          bindings match_res FStar_Tactics_Result.__result)
  =
  fun pat ->
    fun cur_bindings ->
      fun tm ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (299)) (Prims.of_int (4))
                                 (Prims.of_int (299)) (Prims.of_int (13))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (300)) (Prims.of_int (2))
                           (Prims.of_int (330)) (Prims.of_int (19)))))
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
                                                  "FStar.Tactics.PatternMatching.fst"
                                                  (Prims.of_int (299))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (299))
                                                  (Prims.of_int (13))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (300))
                                            (Prims.of_int (2))
                                            (Prims.of_int (330))
                                            (Prims.of_int (19))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (301)) (Prims.of_int (4))
                                      (Prims.of_int (304))
                                      (Prims.of_int (46))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (305)) (Prims.of_int (2))
                                (Prims.of_int (330)) (Prims.of_int (19)))))
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
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (299))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (299))
                                                                   (Prims.of_int (13))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (300))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (330))
                                                             (Prims.of_int (19))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (301))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (304))
                                                       (Prims.of_int (46))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (305))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (330))
                                                 (Prims.of_int (19))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (306))
                                           (Prims.of_int (4))
                                           (Prims.of_int (310))
                                           (Prims.of_int (43))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (311)) (Prims.of_int (2))
                                     (Prims.of_int (330)) (Prims.of_int (19)))))
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
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (46))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (305))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (330))
                                                                  (Prims.of_int (19))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (306))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (310))
                                                            (Prims.of_int (43))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (311))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (330))
                                                      (Prims.of_int (19))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (312))
                                                (Prims.of_int (4))
                                                (Prims.of_int (314))
                                                (Prims.of_int (43))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (315))
                                          (Prims.of_int (2))
                                          (Prims.of_int (330))
                                          (Prims.of_int (19)))))
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
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (43))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (312))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (314))
                                                                 (Prims.of_int (43))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (315))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (330))
                                                           (Prims.of_int (19))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (316))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (321))
                                                     (Prims.of_int (43))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (322))
                                               (Prims.of_int (4))
                                               (Prims.of_int (330))
                                               (Prims.of_int (19)))))
                              with
                              | true ->
                                  ((match pat with
                                    | PAny ->
                                        (fun s ->
                                           FStar_Tactics_Result.Success
                                             ((return []), s))
                                    | PVar var ->
                                        (fun s ->
                                           FStar_Tactics_Result.Success
                                             ((match FStar_List_Tot_Base.assoc
                                                       var cur_bindings
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   tm' ->
                                                   if
                                                     FStar_Reflection_Builtins.term_eq
                                                       tm tm'
                                                   then return cur_bindings
                                                   else
                                                     raise
                                                       (NonLinearMismatch
                                                          (var, tm, tm'))
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   return ((var, tm) ::
                                                     cur_bindings)), s))
                                    | PQn qn1 ->
                                        (fun ps1 ->
                                           match (FStar_Tactics_Builtins.inspect
                                                    tm)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (306))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (306))
                                                               (Prims.of_int (20))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a, ps') ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (306))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (306))
                                                                 (Prims.of_int (20)))))
                                                with
                                                | true ->
                                                    ((match a with
                                                      | FStar_Reflection_Data.Tv_FVar
                                                          fv ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               ((if
                                                                   (FStar_Reflection_Derived.fv_to_string
                                                                    fv) = qn1
                                                                 then
                                                                   return
                                                                    cur_bindings
                                                                 else
                                                                   raise
                                                                    (NameMismatch
                                                                    (qn1,
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv)))),
                                                                 s))
                                                      | uu___ ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               ((raise
                                                                   (SimpleMismatch
                                                                    (pat, tm))),
                                                                 s))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (306))
                                                                  (Prims.of_int (10))
                                                                  (Prims.of_int (306))
                                                                  (Prims.of_int (20)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e, ps') ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'))
                                    | PType ->
                                        (fun ps1 ->
                                           match (FStar_Tactics_Builtins.inspect
                                                    tm)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (312))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (312))
                                                               (Prims.of_int (20))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a, ps') ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (312))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (312))
                                                                 (Prims.of_int (20)))))
                                                with
                                                | true ->
                                                    ((match a with
                                                      | FStar_Reflection_Data.Tv_Type
                                                          () ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               ((return
                                                                   cur_bindings),
                                                                 s))
                                                      | uu___ ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               ((raise
                                                                   (SimpleMismatch
                                                                    (pat, tm))),
                                                                 s))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (312))
                                                                  (Prims.of_int (10))
                                                                  (Prims.of_int (312))
                                                                  (Prims.of_int (20)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e, ps') ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'))
                                    | PApp (p_hd, p_arg) ->
                                        (fun ps1 ->
                                           match (FStar_Tactics_Builtins.inspect
                                                    tm)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (316))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (316))
                                                               (Prims.of_int (20))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a, ps') ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (316))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (316))
                                                                 (Prims.of_int (20)))))
                                                with
                                                | true ->
                                                    ((match a with
                                                      | FStar_Reflection_Data.Tv_App
                                                          (hd, (arg, uu___))
                                                          ->
                                                          (fun ps2 ->
                                                             match (interp_pattern_aux
                                                                    p_hd
                                                                    cur_bindings
                                                                    hd)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (57))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (21)))))
                                                                  with
                                                                  | true ->
                                                                    (bind a1
                                                                    (fun
                                                                    with_hd
                                                                    ->
                                                                    fun ps3
                                                                    ->
                                                                    match 
                                                                    (interp_pattern_aux
                                                                    p_arg
                                                                    with_hd
                                                                    arg)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (55))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (bind a2
                                                                    (fun
                                                                    with_arg
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((return
                                                                    with_arg),
                                                                    s)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (21)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (21)))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'1) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'1))
                                                      | uu___ ->
                                                          (fun s ->
                                                             FStar_Tactics_Result.Success
                                                               ((raise
                                                                   (SimpleMismatch
                                                                    (pat, tm))),
                                                                 s))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (316))
                                                                  (Prims.of_int (10))
                                                                  (Prims.of_int (316))
                                                                  (Prims.of_int (20)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e, ps') ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'))
                                    | uu___ -> FStar_Tactics_Derived.fail "?"))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (43))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (312))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (314))
                                                                  (Prims.of_int (43))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (315))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (330))
                                                            (Prims.of_int (19))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (316))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (321))
                                                      (Prims.of_int (43))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (322))
                                                (Prims.of_int (4))
                                                (Prims.of_int (330))
                                                (Prims.of_int (19))))))))))
let (interp_pattern :
  pattern ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        bindings match_res FStar_Tactics_Result.__result)
  =
  fun pat ->
    fun tm ->
      fun ps ->
        match (interp_pattern_aux pat [] tm)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (336)) (Prims.of_int (21))
                            (Prims.of_int (336)) (Prims.of_int (49))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (336)) (Prims.of_int (4))
                              (Prims.of_int (337)) (Prims.of_int (43)))))
             with
             | true ->
                 (bind a
                    (fun rev_bindings ->
                       fun s ->
                         FStar_Tactics_Result.Success
                           ((return (FStar_List_Tot_Base.rev rev_bindings)),
                             s)))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (336)) (Prims.of_int (4))
                               (Prims.of_int (337)) (Prims.of_int (43)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (match_term :
  pattern ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        bindings FStar_Tactics_Result.__result)
  =
  fun pat ->
    fun tm ->
      fun ps ->
        match match (FStar_Tactics_Derived.norm_term [] tm)
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (343))
                                        (Prims.of_int (10))
                                        (Prims.of_int (343))
                                        (Prims.of_int (46))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (343)) (Prims.of_int (29))
                                  (Prims.of_int (343)) (Prims.of_int (46))))))
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (343)) (Prims.of_int (10))
                                    (Prims.of_int (343)) (Prims.of_int (46)))))
                   with
                   | true ->
                       (interp_pattern pat a)
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (343)) (Prims.of_int (10))
                                     (Prims.of_int (343)) (Prims.of_int (46)))))))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (343)) (Prims.of_int (4))
                              (Prims.of_int (345)) (Prims.of_int (63)))))
             with
             | true ->
                 ((match a with
                   | Success bb ->
                       (fun s -> FStar_Tactics_Result.Success (bb, s))
                   | Failure ex ->
                       (fun ps1 ->
                          match (string_of_match_exception ex)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (345))
                                              (Prims.of_int (33))
                                              (Prims.of_int (345))
                                              (Prims.of_int (63))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (345))
                                                (Prims.of_int (20))
                                                (Prims.of_int (345))
                                                (Prims.of_int (63)))))
                               with
                               | true ->
                                   (FStar_Tactics_Derived.fail a1)
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (345))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (345))
                                                 (Prims.of_int (63)))))))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (343)) (Prims.of_int (4))
                               (Prims.of_int (345)) (Prims.of_int (63)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let debug :
  'uuuuu .
    'uuuuu ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  = fun msg -> fun s -> FStar_Tactics_Result.Success ((), s)
type absvar = FStar_Reflection_Types.binder
type hypothesis = FStar_Reflection_Types.binder
type matching_problem =
  {
  mp_vars: varname Prims.list ;
  mp_hyps: (varname * pattern) Prims.list ;
  mp_goal: pattern FStar_Pervasives_Native.option }
let (__proj__Mkmatching_problem__item__mp_vars :
  matching_problem -> varname Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_vars
let (__proj__Mkmatching_problem__item__mp_hyps :
  matching_problem -> (varname * pattern) Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_hyps
let (__proj__Mkmatching_problem__item__mp_goal :
  matching_problem -> pattern FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_goal
let (string_of_matching_problem : matching_problem -> Prims.string) =
  fun mp ->
    let vars = FStar_String.concat ", " mp.mp_vars in
    let hyps =
      FStar_String.concat "\n        "
        (FStar_List_Tot_Base.map
           (fun uu___ ->
              match uu___ with
              | (nm, pat) ->
                  Prims.strcat nm (Prims.strcat ": " (string_of_pattern pat)))
           mp.mp_hyps) in
    let goal =
      match mp.mp_goal with
      | FStar_Pervasives_Native.None -> "_"
      | FStar_Pervasives_Native.Some pat -> string_of_pattern pat in
    Prims.strcat "\n{ vars: "
      (Prims.strcat vars
         (Prims.strcat "\n"
            (Prims.strcat "  hyps: "
               (Prims.strcat hyps
                  (Prims.strcat "\n"
                     (Prims.strcat "  goal: " (Prims.strcat goal " }")))))))
type matching_solution =
  {
  ms_vars: (varname * FStar_Reflection_Types.term) Prims.list ;
  ms_hyps: (varname * hypothesis) Prims.list }
let (__proj__Mkmatching_solution__item__ms_vars :
  matching_solution -> (varname * FStar_Reflection_Types.term) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_vars
let (__proj__Mkmatching_solution__item__ms_hyps :
  matching_solution -> (varname * hypothesis) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_hyps
let (string_of_matching_solution :
  matching_solution ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun ms ->
    fun ps ->
      match match (FStar_Tactics_Util.map
                     (fun uu___ ->
                        fun s ->
                          FStar_Tactics_Result.Success
                            ((match uu___ with
                              | (varname1, tm) ->
                                  Prims.strcat varname1
                                    (Prims.strcat ": "
                                       (FStar_Reflection_Builtins.term_to_string
                                          tm))), s)) ms.ms_vars)
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (392)) (Prims.of_int (4))
                                      (Prims.of_int (394))
                                      (Prims.of_int (57))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (393)) (Prims.of_int (6))
                                (Prims.of_int (394)) (Prims.of_int (57))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (392)) (Prims.of_int (4))
                                  (Prims.of_int (394)) (Prims.of_int (57)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((FStar_String.concat "\n            " a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (392)) (Prims.of_int (4))
                                     (Prims.of_int (394)) (Prims.of_int (57))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (395)) (Prims.of_int (2))
                            (Prims.of_int (400)) (Prims.of_int (26)))))
           with
           | true ->
               (match match (FStar_Tactics_Util.map
                               (fun uu___ ->
                                  fun s ->
                                    FStar_Tactics_Result.Success
                                      ((match uu___ with
                                        | (nm, binder) ->
                                            Prims.strcat nm
                                              (Prims.strcat ": "
                                                 (FStar_Reflection_Derived.binder_to_string
                                                    binder))), s)) ms.ms_hyps)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (395))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (400))
                                                      (Prims.of_int (26))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (396))
                                                (Prims.of_int (4))
                                                (Prims.of_int (398))
                                                (Prims.of_int (58))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (397))
                                          (Prims.of_int (6))
                                          (Prims.of_int (398))
                                          (Prims.of_int (58))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (396))
                                            (Prims.of_int (4))
                                            (Prims.of_int (398))
                                            (Prims.of_int (58)))))
                           with
                           | true ->
                               FStar_Tactics_Result.Success
                                 ((FStar_String.concat "\n        " a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (396))
                                               (Prims.of_int (4))
                                               (Prims.of_int (398))
                                               (Prims.of_int (58))))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "prims.fst"
                                      (Prims.of_int (603))
                                      (Prims.of_int (19))
                                      (Prims.of_int (603))
                                      (Prims.of_int (31)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           ((Prims.strcat "\n{ vars: "
                               (Prims.strcat a
                                  (Prims.strcat "\n"
                                     (Prims.strcat "  hyps: "
                                        (Prims.strcat a1 " }"))))),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   ps'1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "prims.fst"
                                         (Prims.of_int (603))
                                         (Prims.of_int (19))
                                         (Prims.of_int (603))
                                         (Prims.of_int (31))))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let assoc_varname_fail :
  'b .
    varname ->
      (varname * 'b) Prims.list ->
        FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun key ->
    fun ls ->
      match FStar_List_Tot_Base.assoc key ls with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Derived.fail (Prims.strcat "Not found: " key)
      | FStar_Pervasives_Native.Some x ->
          (fun s -> FStar_Tactics_Result.Success (x, s))
let ms_locate_hyp :
  'a .
    matching_solution ->
      varname ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.binder FStar_Tactics_Result.__result
  = fun solution -> fun name -> assoc_varname_fail name solution.ms_hyps
let ms_locate_var :
  'a .
    matching_solution ->
      varname ->
        FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun solution ->
    fun name ->
      fun ps ->
        match (assoc_varname_fail name solution.ms_vars)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (415)) (Prims.of_int (13))
                            (Prims.of_int (415)) (Prims.of_int (55))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (415)) (Prims.of_int (2))
                              (Prims.of_int (415)) (Prims.of_int (55)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.unquote a1)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (415)) (Prims.of_int (2))
                               (Prims.of_int (415)) (Prims.of_int (55)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let ms_locate_unit :
  'uuuuu 'uuuuu1 'a .
    'uuuuu ->
      'uuuuu1 ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun _solution ->
    fun _binder_name -> fun s -> FStar_Tactics_Result.Success ((), s)
let rec solve_mp_for_single_hyp :
  'a .
    varname ->
      pattern ->
        hypothesis Prims.list ->
          (matching_solution ->
             FStar_Tactics_Types.proofstate ->
               'a FStar_Tactics_Result.__result)
            ->
            matching_solution ->
              FStar_Tactics_Types.proofstate ->
                'a FStar_Tactics_Result.__result
  =
  fun name ->
    fun pat ->
      fun hypotheses ->
        fun body ->
          fun part_sol ->
            match hypotheses with
            | [] -> FStar_Tactics_Derived.fail "No matching hypothesis"
            | h::hs ->
                FStar_Tactics_Derived.or_else
                  (fun uu___ ->
                     fun ps ->
                       match (interp_pattern_aux pat part_sol.ms_vars
                                (FStar_Reflection_Derived.type_of_binder h))
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (455))
                                           (Prims.of_int (15))
                                           (Prims.of_int (455))
                                           (Prims.of_int (73))))))
                       with
                       | FStar_Tactics_Result.Success (a1, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (455))
                                             (Prims.of_int (9))
                                             (Prims.of_int (460))
                                             (Prims.of_int (73)))))
                            with
                            | true ->
                                ((match a1 with
                                  | Failure ex ->
                                      (fun ps1 ->
                                         match match (string_of_match_exception
                                                        ex)
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (74))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (457))
                                                                   (Prims.of_int (43))
                                                                   (Prims.of_int (457))
                                                                   (Prims.of_int (73))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a2, ps'1) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
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
                                                              "Failed to match hyp: "
                                                              a2),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e, ps'1) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e, ps'1)
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a2, ps'1) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (457))
                                                               (Prims.of_int (11))
                                                               (Prims.of_int (457))
                                                               (Prims.of_int (74)))))
                                              with
                                              | true ->
                                                  (FStar_Tactics_Derived.fail
                                                     a2)
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (457))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (457))
                                                                (Prims.of_int (74)))))))
                                         | FStar_Tactics_Result.Failed
                                             (e, ps'1) ->
                                             FStar_Tactics_Result.Failed
                                               (e, ps'1))
                                  | Success bindings1 ->
                                      (fun ps1 ->
                                         match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (459))
                                                                (Prims.of_int (35))
                                                                (Prims.of_int (459))
                                                                (Prims.of_int (37))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (460))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (460))
                                                          (Prims.of_int (73)))))
                                         with
                                         | true ->
                                             (body
                                                {
                                                  ms_vars = bindings1;
                                                  ms_hyps = ((name, h) ::
                                                    (part_sol.ms_hyps))
                                                })
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (459))
                                                                 (Prims.of_int (35))
                                                                 (Prims.of_int (459))
                                                                 (Prims.of_int (37))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (460))
                                                           (Prims.of_int (11))
                                                           (Prims.of_int (460))
                                                           (Prims.of_int (73)))))))))
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (455))
                                              (Prims.of_int (9))
                                              (Prims.of_int (460))
                                              (Prims.of_int (73)))))))
                       | FStar_Tactics_Result.Failed (e, ps') ->
                           FStar_Tactics_Result.Failed (e, ps'))
                  (fun uu___ ->
                     solve_mp_for_single_hyp name pat hs body part_sol)
let rec solve_mp_for_hyps :
  'a .
    (varname * pattern) Prims.list ->
      hypothesis Prims.list ->
        (matching_solution ->
           FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
          ->
          matching_solution ->
            FStar_Tactics_Types.proofstate ->
              'a FStar_Tactics_Result.__result
  =
  fun mp_hyps ->
    fun hypotheses ->
      fun body ->
        fun partial_solution ->
          match mp_hyps with
          | [] -> body partial_solution
          | (name, pat)::pats ->
              solve_mp_for_single_hyp name pat hypotheses
                (solve_mp_for_hyps pats hypotheses body) partial_solution
let solve_mp :
  'a .
    matching_problem ->
      FStar_Reflection_Types.binders ->
        FStar_Reflection_Types.term ->
          (matching_solution ->
             FStar_Tactics_Types.proofstate ->
               'a FStar_Tactics_Result.__result)
            ->
            FStar_Tactics_Types.proofstate ->
              'a FStar_Tactics_Result.__result
  =
  fun problem ->
    fun hypotheses ->
      fun goal ->
        fun body ->
          fun ps ->
            match (match problem.mp_goal with
                   | FStar_Pervasives_Native.None ->
                       (fun s ->
                          FStar_Tactics_Result.Success
                            ({ ms_vars = []; ms_hyps = [] }, s))
                   | FStar_Pervasives_Native.Some pat ->
                       (fun ps1 ->
                          match (interp_pattern pat goal)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (491))
                                              (Prims.of_int (12))
                                              (Prims.of_int (491))
                                              (Prims.of_int (35))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (491))
                                                (Prims.of_int (6))
                                                (Prims.of_int (493))
                                                (Prims.of_int (64)))))
                               with
                               | true ->
                                   ((match a1 with
                                     | Failure ex ->
                                         (fun ps2 ->
                                            match match (string_of_match_exception
                                                           ex)
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (86))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (85))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a2, ps'1) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
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
                                                                 "Failed to match goal: "
                                                                 a2),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e, ps'1) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e, ps'1)
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2, ps'1) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (492))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (492))
                                                                  (Prims.of_int (86)))))
                                                 with
                                                 | true ->
                                                     (FStar_Tactics_Derived.fail
                                                        a2)
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (492))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (492))
                                                                   (Prims.of_int (86)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'1) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'1))
                                     | Success bindings1 ->
                                         (fun s ->
                                            FStar_Tactics_Result.Success
                                              ({
                                                 ms_vars = bindings1;
                                                 ms_hyps = []
                                               }, s))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (491))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (493))
                                                 (Prims.of_int (64)))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps')))
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (488)) (Prims.of_int (4))
                                (Prims.of_int (493)) (Prims.of_int (64))))))
            with
            | FStar_Tactics_Result.Success (a1, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (494)) (Prims.of_int (2))
                                  (Prims.of_int (494)) (Prims.of_int (62)))))
                 with
                 | true ->
                     (solve_mp_for_hyps problem.mp_hyps hypotheses body a1)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (494)) (Prims.of_int (2))
                                   (Prims.of_int (494)) (Prims.of_int (62)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
let __ : 't . unit -> 't = fun uu___ -> failwith "Not yet implemented:__"
let (any_qn : Prims.string) = "FStar.Tactics.PatternMatching.__"
let rec (pattern_of_term_ex :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      pattern match_res FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (517)) (Prims.of_int (8))
                          (Prims.of_int (517)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (517)) (Prims.of_int (2))
                            (Prims.of_int (535)) (Prims.of_int (44)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_Var bv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((return
                              (PVar (FStar_Reflection_Derived.name_of_bv bv))),
                            s))
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((return
                              (if
                                 (FStar_Reflection_Derived.fv_to_string fv) =
                                   any_qn
                               then PAny
                               else
                                 PQn
                                   (FStar_Reflection_Derived.fv_to_string fv))),
                            s))
                 | FStar_Reflection_Data.Tv_Type () ->
                     (fun s ->
                        FStar_Tactics_Result.Success ((return PType), s))
                 | FStar_Reflection_Data.Tv_App (f, (x, uu___)) ->
                     (fun ps1 ->
                        match match (FStar_Tactics_Builtins.inspect f)
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (526))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (528))
                                                        (Prims.of_int (29))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.PatternMatching.fst"
                                                  (Prims.of_int (526))
                                                  (Prims.of_int (23))
                                                  (Prims.of_int (526))
                                                  (Prims.of_int (32))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (526))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (528))
                                                    (Prims.of_int (29)))))
                                   with
                                   | true ->
                                       ((match a1 with
                                         | FStar_Reflection_Data.Tv_FVar fv
                                             ->
                                             (fun s ->
                                                FStar_Tactics_Result.Success
                                                  (((FStar_Reflection_Derived.fv_to_string
                                                       fv)
                                                      = any_qn), s))
                                         | uu___1 ->
                                             (fun s ->
                                                FStar_Tactics_Result.Success
                                                  (false, s))))
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (526))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (528))
                                                     (Prims.of_int (29)))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (529))
                                              (Prims.of_int (4))
                                              (Prims.of_int (534))
                                              (Prims.of_int (31)))))
                             with
                             | true ->
                                 (if a1
                                  then
                                    (fun s ->
                                       FStar_Tactics_Result.Success
                                         ((return PAny), s))
                                  else
                                    (fun ps2 ->
                                       match (pattern_of_term_ex f)
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps2
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (532))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (532))
                                                           (Prims.of_int (36))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a2, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (532))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (534))
                                                             (Prims.of_int (31)))))
                                            with
                                            | true ->
                                                (bind a2
                                                   (fun fpat ->
                                                      fun ps3 ->
                                                        match (pattern_of_term_ex
                                                                 x)
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (36))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a3, ps'3) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (30)))))
                                                             with
                                                             | true ->
                                                                 (bind a3
                                                                    (
                                                                    fun xpat
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((return
                                                                    (PApp
                                                                    (fpat,
                                                                    xpat))),
                                                                    s)))
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (30)))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'3) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'3)))
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (532))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (534))
                                                              (Prims.of_int (31)))))))
                                       | FStar_Tactics_Result.Failed
                                           (e, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'2)))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (529))
                                               (Prims.of_int (4))
                                               (Prims.of_int (534))
                                               (Prims.of_int (31)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((raise (UnsupportedTermInPattern tm)), s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (517)) (Prims.of_int (2))
                             (Prims.of_int (535)) (Prims.of_int (44)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (beta_reduce :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  = fun tm -> FStar_Tactics_Derived.norm_term [] tm
let (pattern_of_term :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> pattern FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (pattern_of_term_ex tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (545)) (Prims.of_int (10))
                          (Prims.of_int (545)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (545)) (Prims.of_int (4))
                            (Prims.of_int (547)) (Prims.of_int (63)))))
           with
           | true ->
               ((match a with
                 | Success bb ->
                     (fun s -> FStar_Tactics_Result.Success (bb, s))
                 | Failure ex ->
                     (fun ps1 ->
                        match (string_of_match_exception ex)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (547))
                                            (Prims.of_int (33))
                                            (Prims.of_int (547))
                                            (Prims.of_int (63))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (547))
                                              (Prims.of_int (20))
                                              (Prims.of_int (547))
                                              (Prims.of_int (63)))))
                             with
                             | true ->
                                 (FStar_Tactics_Derived.fail a1)
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (547))
                                               (Prims.of_int (20))
                                               (Prims.of_int (547))
                                               (Prims.of_int (63)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (545)) (Prims.of_int (4))
                             (Prims.of_int (547)) (Prims.of_int (63)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
type 'a hyp = FStar_Reflection_Types.binder
type 'a pm_goal = unit
let (hyp_qn : Prims.string) = "FStar.Tactics.PatternMatching.hyp"
let (goal_qn : Prims.string) = "FStar.Tactics.PatternMatching.pm_goal"
type abspat_binder_kind =
  | ABKVar of FStar_Reflection_Types.typ 
  | ABKHyp 
  | ABKGoal 
let (uu___is_ABKVar : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKVar _0 -> true | uu___ -> false
let (__proj__ABKVar__item___0 :
  abspat_binder_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | ABKVar _0 -> _0
let (uu___is_ABKHyp : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKHyp -> true | uu___ -> false
let (uu___is_ABKGoal : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKGoal -> true | uu___ -> false
let (string_of_abspat_binder_kind : abspat_binder_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ABKVar uu___1 -> "varname"
    | ABKHyp -> "hyp"
    | ABKGoal -> "goal"
type abspat_argspec = {
  asa_name: absvar ;
  asa_kind: abspat_binder_kind }
let (__proj__Mkabspat_argspec__item__asa_name : abspat_argspec -> absvar) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_name
let (__proj__Mkabspat_argspec__item__asa_kind :
  abspat_argspec -> abspat_binder_kind) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_kind
type abspat_continuation =
  (abspat_argspec Prims.list * FStar_Reflection_Types.term)
let (classify_abspat_binder :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate ->
      (abspat_binder_kind * FStar_Reflection_Types.term)
        FStar_Tactics_Result.__result)
  =
  fun binder ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (599)) (Prims.of_int (16))
                             (Prims.of_int (599)) (Prims.of_int (19))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                       (Prims.of_int (600)) (Prims.of_int (2))
                       (Prims.of_int (611)) (Prims.of_int (34)))))
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
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (599))
                                              (Prims.of_int (16))
                                              (Prims.of_int (599))
                                              (Prims.of_int (19))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (600))
                                        (Prims.of_int (2))
                                        (Prims.of_int (611))
                                        (Prims.of_int (34))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (600)) (Prims.of_int (16))
                                  (Prims.of_int (600)) (Prims.of_int (48))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (601)) (Prims.of_int (2))
                            (Prims.of_int (611)) (Prims.of_int (34)))))
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
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (599))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (599))
                                                               (Prims.of_int (19))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (600))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (611))
                                                         (Prims.of_int (34))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (600))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (600))
                                                   (Prims.of_int (48))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (601))
                                             (Prims.of_int (2))
                                             (Prims.of_int (611))
                                             (Prims.of_int (34))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (601))
                                       (Prims.of_int (17))
                                       (Prims.of_int (601))
                                       (Prims.of_int (50))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (603)) (Prims.of_int (2))
                                 (Prims.of_int (611)) (Prims.of_int (34)))))
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
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (19))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (34))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (48))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (601))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (611))
                                                              (Prims.of_int (34))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (50))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.PatternMatching.fst"
                                                  (Prims.of_int (603))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (34))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (603))
                                            (Prims.of_int (12))
                                            (Prims.of_int (603))
                                            (Prims.of_int (33))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (604)) (Prims.of_int (2))
                                      (Prims.of_int (611))
                                      (Prims.of_int (34)))))
                     with
                     | true ->
                         (match (interp_pattern
                                   (PApp ((PQn hyp_qn), (PVar "v")))
                                   (FStar_Reflection_Derived.type_of_binder
                                      binder))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (599))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (34))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (601))
                                                                    (Prims.of_int (50))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (603))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (34))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (33))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (604))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (34))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (604))
                                              (Prims.of_int (8))
                                              (Prims.of_int (604))
                                              (Prims.of_int (34))))))
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (604))
                                                (Prims.of_int (2))
                                                (Prims.of_int (611))
                                                (Prims.of_int (34)))))
                               with
                               | true ->
                                   ((match a with
                                     | Success ((uu___, hyp_typ)::[]) ->
                                         (fun s ->
                                            FStar_Tactics_Result.Success
                                              ((ABKHyp, hyp_typ), s))
                                     | Success uu___ ->
                                         FStar_Tactics_Derived.fail
                                           "classifiy_abspat_binder: impossible (1)"
                                     | Failure uu___ ->
                                         (fun ps1 ->
                                            match (interp_pattern
                                                     (PApp
                                                        ((PQn goal_qn),
                                                          (PVar "v")))
                                                     (FStar_Reflection_Derived.type_of_binder
                                                        binder))
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (608))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (608))
                                                                (Prims.of_int (37))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a1, ps'1) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (608))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (34)))))
                                                 with
                                                 | true ->
                                                     ((match a1 with
                                                       | Success
                                                           ((uu___1,
                                                             goal_typ)::[])
                                                           ->
                                                           (fun s ->
                                                              FStar_Tactics_Result.Success
                                                                ((ABKGoal,
                                                                   goal_typ),
                                                                  s))
                                                       | Success uu___1 ->
                                                           FStar_Tactics_Derived.fail
                                                             "classifiy_abspat_binder: impossible (2)"
                                                       | Failure uu___1 ->
                                                           (fun s ->
                                                              FStar_Tactics_Result.Success
                                                                (((ABKVar
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    binder)),
                                                                   (FStar_Reflection_Derived.type_of_binder
                                                                    binder)),
                                                                  s))))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (608))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (611))
                                                                   (Prims.of_int (34)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'1) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'1))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (604))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (34)))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps')))))
let rec (binders_and_body_of_abs :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binders * FStar_Reflection_Types.term)
        FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (615)) (Prims.of_int (8))
                          (Prims.of_int (615)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (615)) (Prims.of_int (2))
                            (Prims.of_int (619)) (Prims.of_int (15)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_Abs (binder, tm1) ->
                     (fun ps1 ->
                        match (binders_and_body_of_abs tm1)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (617))
                                            (Prims.of_int (24))
                                            (Prims.of_int (617))
                                            (Prims.of_int (50))))))
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (617))
                                              (Prims.of_int (4))
                                              (Prims.of_int (618))
                                              (Prims.of_int (27)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   (((match a1 with
                                      | (binders, body) ->
                                          ((binder :: binders), body))),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (617))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (618))
                                                 (Prims.of_int (27))))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ ->
                     (fun s -> FStar_Tactics_Result.Success (([], tm), s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (615)) (Prims.of_int (2))
                             (Prims.of_int (619)) (Prims.of_int (15)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (cleanup_abspat :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  = fun t -> FStar_Tactics_Derived.norm_term [] t
let (matching_problem_of_abs :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (matching_problem * abspat_continuation) FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match match (cleanup_abspat tm)
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (641))
                                      (Prims.of_int (22))
                                      (Prims.of_int (641))
                                      (Prims.of_int (65))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (641)) (Prims.of_int (46))
                                (Prims.of_int (641)) (Prims.of_int (65))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (641)) (Prims.of_int (22))
                                  (Prims.of_int (641)) (Prims.of_int (65)))))
                 with
                 | true ->
                     (binders_and_body_of_abs a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (641)) (Prims.of_int (22))
                                   (Prims.of_int (641)) (Prims.of_int (65)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (641)) (Prims.of_int (2))
                            (Prims.of_int (680)) (Prims.of_int (18)))))
           with
           | true ->
               ((match a with
                 | (binders, body) ->
                     (fun ps1 ->
                        match match match match (FStar_Tactics_Util.map
                                                   (fun b ->
                                                      fun s ->
                                                        FStar_Tactics_Result.Success
                                                          ((FStar_Reflection_Derived.name_of_binder
                                                              b), s)) binders)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (66))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (66))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (65))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (643))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (643))
                                                              (Prims.of_int (64))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a1, ps'1) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (642))
                                                                (Prims.of_int (27))
                                                                (Prims.of_int (643))
                                                                (Prims.of_int (65)))))
                                               with
                                               | true ->
                                                   FStar_Tactics_Result.Success
                                                     ((FStar_String.concat
                                                         ", " a1),
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (642))
                                                                   (Prims.of_int (27))
                                                                   (Prims.of_int (643))
                                                                   (Prims.of_int (65))))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'1) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'1)
                                    with
                                    | FStar_Tactics_Result.Success (a1, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
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
                                               ((Prims.strcat "Got binders: "
                                                   a1),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (603))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (603))
                                                             (Prims.of_int (31))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (642))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (643))
                                                    (Prims.of_int (66)))))
                                   with
                                   | true ->
                                       (debug a1)
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (643))
                                                     (Prims.of_int (66)))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (645))
                                              (Prims.of_int (2))
                                              (Prims.of_int (680))
                                              (Prims.of_int (18)))))
                             with
                             | true ->
                                 (match (FStar_Tactics_Util.map
                                           (fun binder ->
                                              fun ps2 ->
                                                match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (43))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (648))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (651))
                                                                 (Prims.of_int (43)))))
                                                with
                                                | true ->
                                                    (match (debug
                                                              (Prims.strcat
                                                                 "Got binder: "
                                                                 (Prims.strcat
                                                                    (
                                                                    FStar_Reflection_Derived.name_of_binder
                                                                    binder)
                                                                    (
                                                                    Prims.strcat
                                                                    "; type is "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    binder))))))
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (43))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (54))))))
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a2, ps'2) ->
                                                         (match FStar_Tactics_Types.tracepoint
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (43)))))
                                                          with
                                                          | true ->
                                                              (match 
                                                                 (classify_abspat_binder
                                                                    binder)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (60))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a3
                                                                    with
                                                                    | 
                                                                    (binder_kind,
                                                                    typ) ->
                                                                    (binder,
                                                                    (FStar_Reflection_Derived.name_of_binder
                                                                    binder),
                                                                    binder_kind,
                                                                    typ))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (28))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e, ps'3)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                     | FStar_Tactics_Result.Failed
                                                         (e, ps'2) ->
                                                         FStar_Tactics_Result.Failed
                                                           (e, ps'2)))
                                           binders)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (645))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (680))
                                                            (Prims.of_int (18))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (646))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (652))
                                                      (Prims.of_int (13))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (654))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (680))
                                                        (Prims.of_int (18)))))
                                       with
                                       | true ->
                                           (match (FStar_Tactics_Util.fold_left
                                                     (fun problem ->
                                                        fun uu___ ->
                                                          match uu___ with
                                                          | (binder, bv_name,
                                                             binder_kind,
                                                             typ) ->
                                                              (fun ps2 ->
                                                                 match 
                                                                   (debug
                                                                    (Prims.strcat
                                                                    "Compiling binder "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Derived.name_of_binder
                                                                    binder)
                                                                    (Prims.strcat
                                                                    ", classified as "
                                                                    (Prims.strcat
                                                                    (string_of_abspat_binder_kind
                                                                    binder_kind)
                                                                    (Prims.strcat
                                                                    ", with type "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    typ)))))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (52))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (48)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match binder_kind
                                                                    with
                                                                    | ABKVar
                                                                    uu___1 ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ({
                                                                    mp_vars =
                                                                    (bv_name
                                                                    ::
                                                                    (problem.mp_vars));
                                                                    mp_hyps =
                                                                    (problem.mp_hyps);
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    }, s))
                                                                    | ABKHyp
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (pattern_of_term
                                                                    typ)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (47))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (78))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (77))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (78)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((bv_name,
                                                                    a4),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (78))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (47)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a4 ::
                                                                    (problem.mp_hyps)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (47))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (63)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ({
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    a4;
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    },
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (63))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | ABKGoal
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    (pattern_of_term
                                                                    typ)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    a4),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ({
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    (problem.mp_hyps);
                                                                    mp_goal =
                                                                    a4
                                                                    },
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (73))))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (48)))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                     {
                                                       mp_vars = [];
                                                       mp_hyps = [];
                                                       mp_goal =
                                                         FStar_Pervasives_Native.None
                                                     } a2)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (654))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (655))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (666))
                                                                (Prims.of_int (24))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (668))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (680))
                                                                  (Prims.of_int (18)))))
                                                 with
                                                 | true ->
                                                     (match match FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57)))))
                                                            with
                                                            | true ->
                                                                (match 
                                                                   (FStar_Tactics_Util.map
                                                                    (fun xx
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((match xx
                                                                    with
                                                                    | (binder,
                                                                    xx1,
                                                                    binder_kind,
                                                                    yy) ->
                                                                    {
                                                                    asa_name
                                                                    = binder;
                                                                    asa_kind
                                                                    =
                                                                    binder_kind
                                                                    }), s))
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (52))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'4) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a4, tm),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (57))))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18)))))
                                                           with
                                                           | true ->
                                                               (match 
                                                                  FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18)))))
                                                                with
                                                                | true ->
                                                                    (
                                                                    match 
                                                                    (debug
                                                                    (Prims.strcat
                                                                    "Got matching problem: "
                                                                    (string_of_matching_problem
                                                                    {
                                                                    mp_vars =
                                                                    (FStar_List_Tot_Base.rev
                                                                    a3.mp_vars);
                                                                    mp_hyps =
                                                                    (FStar_List_Tot_Base.rev
                                                                    a3.mp_hyps);
                                                                    mp_goal =
                                                                    (a3.mp_goal)
                                                                    })))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (68))))))
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
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (({
                                                                    mp_vars =
                                                                    (FStar_List_Tot_Base.rev
                                                                    a3.mp_vars);
                                                                    mp_hyps =
                                                                    (FStar_List_Tot_Base.rev
                                                                    a3.mp_hyps);
                                                                    mp_goal =
                                                                    (a3.mp_goal)
                                                                    }, a4),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (18))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
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
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (641)) (Prims.of_int (2))
                             (Prims.of_int (680)) (Prims.of_int (18)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (arg_type_of_binder_kind :
  abspat_binder_kind ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun binder_kind ->
    fun s ->
      FStar_Tactics_Result.Success
        ((match binder_kind with
          | ABKVar typ -> typ
          | ABKHyp ->
              FStar_Reflection_Builtins.pack_ln
                (FStar_Reflection_Data.Tv_FVar
                   (FStar_Reflection_Builtins.pack_fv
                      ["FStar"; "Reflection"; "Types"; "binder"]))
          | ABKGoal ->
              FStar_Reflection_Builtins.pack_ln
                (FStar_Reflection_Data.Tv_FVar
                   (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"]))),
          s)
let (locate_fn_of_binder_kind :
  abspat_binder_kind -> FStar_Reflection_Types.term) =
  fun binder_kind ->
    match binder_kind with
    | ABKVar uu___ ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_var"]))
    | ABKHyp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_hyp"]))
    | ABKGoal ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_unit"]))
let (abspat_arg_of_abspat_argspec :
  FStar_Reflection_Types.term ->
    abspat_argspec ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun solution_term ->
    fun argspec ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (707)) (Prims.of_int (15))
                               (Prims.of_int (707)) (Prims.of_int (56))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                         (Prims.of_int (708)) (Prims.of_int (2))
                         (Prims.of_int (711)) (Prims.of_int (27)))))
        with
        | true ->
            (match (FStar_Tactics_Builtins.pack
                      (FStar_Reflection_Data.Tv_Const
                         (FStar_Reflection_Data.C_String
                            (FStar_Reflection_Derived.name_of_binder
                               argspec.asa_name))))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (707))
                                             (Prims.of_int (15))
                                             (Prims.of_int (707))
                                             (Prims.of_int (56))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (708))
                                       (Prims.of_int (2))
                                       (Prims.of_int (711))
                                       (Prims.of_int (27))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (708)) (Prims.of_int (16))
                                 (Prims.of_int (708)) (Prims.of_int (76))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (709)) (Prims.of_int (2))
                                   (Prims.of_int (711)) (Prims.of_int (27)))))
                  with
                  | true ->
                      (match match match (arg_type_of_binder_kind
                                            argspec.asa_kind)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (27))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (709))
                                                                   (Prims.of_int (20))
                                                                   (Prims.of_int (710))
                                                                   (Prims.of_int (72))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (709))
                                                             (Prims.of_int (21))
                                                             (Prims.of_int (709))
                                                             (Prims.of_int (75))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (709))
                                                       (Prims.of_int (22))
                                                       (Prims.of_int (709))
                                                       (Prims.of_int (62))))))
                                   with
                                   | FStar_Tactics_Result.Success (a1, ps'1)
                                       ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (709))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (709))
                                                         (Prims.of_int (75)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((a1,
                                                 FStar_Reflection_Data.Q_Explicit),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (709))
                                                            (Prims.of_int (21))
                                                            (Prims.of_int (709))
                                                            (Prims.of_int (75))))))))
                                   | FStar_Tactics_Result.Failed (e, ps'1) ->
                                       FStar_Tactics_Result.Failed (e, ps'1)
                             with
                             | FStar_Tactics_Result.Success (a1, ps'1) ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (709))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (710))
                                                   (Prims.of_int (72)))))
                                  with
                                  | true ->
                                      FStar_Tactics_Result.Success
                                        ([a1;
                                         (solution_term,
                                           FStar_Reflection_Data.Q_Explicit);
                                         (a,
                                           FStar_Reflection_Data.Q_Explicit)],
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (709))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (710))
                                                      (Prims.of_int (72))))))))
                             | FStar_Tactics_Result.Failed (e, ps'1) ->
                                 FStar_Tactics_Result.Failed (e, ps'1)
                       with
                       | FStar_Tactics_Result.Success (a1, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (711))
                                             (Prims.of_int (2))
                                             (Prims.of_int (711))
                                             (Prims.of_int (27)))))
                            with
                            | true ->
                                FStar_Tactics_Result.Success
                                  ((FStar_Reflection_Derived.mk_app
                                      (locate_fn_of_binder_kind
                                         argspec.asa_kind) a1),
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (711))
                                                (Prims.of_int (2))
                                                (Prims.of_int (711))
                                                (Prims.of_int (27))))))))
                       | FStar_Tactics_Result.Failed (e, ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (specialize_abspat_continuation' :
  abspat_continuation ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun continuation ->
    fun solution_term ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (720)) (Prims.of_int (4))
                               (Prims.of_int (720)) (Prims.of_int (68))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                         (Prims.of_int (721)) (Prims.of_int (2))
                         (Prims.of_int (722)) (Prims.of_int (35)))))
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
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (720))
                                                (Prims.of_int (4))
                                                (Prims.of_int (720))
                                                (Prims.of_int (68))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (721))
                                          (Prims.of_int (2))
                                          (Prims.of_int (722))
                                          (Prims.of_int (35))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (721)) (Prims.of_int (23))
                                    (Prims.of_int (721)) (Prims.of_int (35))))))
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (721)) (Prims.of_int (2))
                              (Prims.of_int (722)) (Prims.of_int (35)))))
             with
             | true ->
                 ((match continuation with
                   | (argspecs, body) ->
                       (fun ps1 ->
                          match (FStar_Tactics_Util.map
                                   (fun argspec ->
                                      fun ps2 ->
                                        match (abspat_arg_of_abspat_argspec
                                                 solution_term argspec)
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (720))
                                                            (Prims.of_int (5))
                                                            (Prims.of_int (720))
                                                            (Prims.of_int (55))))))
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a, ps') ->
                                            (match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (720))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (720))
                                                              (Prims.of_int (68)))))
                                             with
                                             | true ->
                                                 FStar_Tactics_Result.Success
                                                   ((a,
                                                      FStar_Reflection_Data.Q_Explicit),
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (720))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (720))
                                                                 (Prims.of_int (68))))))))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps') ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps')) argspecs)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (722))
                                              (Prims.of_int (14))
                                              (Prims.of_int (722))
                                              (Prims.of_int (35))))))
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (722))
                                                (Prims.of_int (2))
                                                (Prims.of_int (722))
                                                (Prims.of_int (35)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((FStar_Reflection_Derived.mk_app body a),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (722))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (722))
                                                   (Prims.of_int (35))))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps'))))
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
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (720))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (720))
                                                 (Prims.of_int (68))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (721))
                                           (Prims.of_int (2))
                                           (Prims.of_int (722))
                                           (Prims.of_int (35))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (721)) (Prims.of_int (23))
                                     (Prims.of_int (721)) (Prims.of_int (35))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (721)) (Prims.of_int (2))
                               (Prims.of_int (722)) (Prims.of_int (35)))))))
let (specialize_abspat_continuation :
  abspat_continuation ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun continuation ->
    fun ps ->
      match (FStar_Tactics_Derived.fresh_binder
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar";
                        "Tactics";
                        "PatternMatching";
                        "matching_solution"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (729)) (Prims.of_int (24))
                          (Prims.of_int (729)) (Prims.of_int (57))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (730)) (Prims.of_int (2))
                            (Prims.of_int (736)) (Prims.of_int (9)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.pack
                         (FStar_Reflection_Data.Tv_Var
                            (FStar_Reflection_Derived.bv_of_binder a)))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (730))
                                          (Prims.of_int (2))
                                          (Prims.of_int (736))
                                          (Prims.of_int (9))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (730)) (Prims.of_int (22))
                                    (Prims.of_int (730)) (Prims.of_int (66))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (731)) (Prims.of_int (2))
                                      (Prims.of_int (736)) (Prims.of_int (9)))))
                     with
                     | true ->
                         (match (specialize_abspat_continuation' continuation
                                   a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (731))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (736))
                                                    (Prims.of_int (9))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (731))
                                              (Prims.of_int (16))
                                              (Prims.of_int (731))
                                              (Prims.of_int (74))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (732))
                                                (Prims.of_int (2))
                                                (Prims.of_int (736))
                                                (Prims.of_int (9)))))
                               with
                               | true ->
                                   (match (FStar_Tactics_Builtins.pack
                                             (FStar_Reflection_Data.Tv_Abs
                                                (a, a2)))
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (732))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (736))
                                                              (Prims.of_int (9))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (732))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (732))
                                                        (Prims.of_int (53))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'3)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'3
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (733))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (736))
                                                          (Prims.of_int (9)))))
                                         with
                                         | true ->
                                             (match (debug
                                                       (Prims.strcat
                                                          "Specialized into "
                                                          (FStar_Reflection_Builtins.term_to_string
                                                             a3)))
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (9))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (733))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (733))
                                                                  (Prims.of_int (56))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a4, ps'4) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'4
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (9)))))
                                                   with
                                                   | true ->
                                                       (match (beta_reduce a3)
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (38))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a5, ps'5) ->
                                                            (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (9)))))
                                                             with
                                                             | true ->
                                                                 (match 
                                                                    (debug
                                                                    (Prims.strcat
                                                                    "\226\128\166 which reduces to "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a5)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (61))))))
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a6,
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
                                                                    (a3,
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
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'5) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'5)))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'4) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'4)))
                                    | FStar_Tactics_Result.Failed (e, ps'3)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'3)))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let interp_abspat_continuation :
  'a .
    abspat_continuation ->
      FStar_Tactics_Types.proofstate ->
        (matching_solution ->
           FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
          FStar_Tactics_Result.__result
  =
  fun continuation ->
    fun ps ->
      match (specialize_abspat_continuation continuation)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (743)) (Prims.of_int (16))
                          (Prims.of_int (743)) (Prims.of_int (59))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (744)) (Prims.of_int (2))
                            (Prims.of_int (744)) (Prims.of_int (47)))))
           with
           | true ->
               (FStar_Tactics_Builtins.unquote a1)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (744)) (Prims.of_int (2))
                             (Prims.of_int (744)) (Prims.of_int (47)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let interp_abspat :
  'a .
    'a ->
      FStar_Tactics_Types.proofstate ->
        (matching_problem * abspat_continuation)
          FStar_Tactics_Result.__result
  =
  fun abspat ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (754)) (Prims.of_int (26))
                             (Prims.of_int (754)) (Prims.of_int (40))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                       (Prims.of_int (754)) (Prims.of_int (2))
                       (Prims.of_int (754)) (Prims.of_int (40)))))
      with
      | true ->
          (matching_problem_of_abs
             (Obj.magic
                (failwith "Cannot evaluate open quotation at runtime")))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (754)) (Prims.of_int (26))
                              (Prims.of_int (754)) (Prims.of_int (40))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (754)) (Prims.of_int (2))
                        (Prims.of_int (754)) (Prims.of_int (40))))))
let match_abspat :
  'b 'a .
    'a ->
      (abspat_continuation ->
         FStar_Tactics_Types.proofstate ->
           (matching_solution ->
              FStar_Tactics_Types.proofstate ->
                'b FStar_Tactics_Result.__result)
             FStar_Tactics_Result.__result)
        -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun abspat ->
           fun k ->
             fun ps ->
               match (FStar_Tactics_Derived.cur_goal ())
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (762)) (Prims.of_int (13))
                                   (Prims.of_int (762)) (Prims.of_int (24))))))
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   Obj.magic
                     (Obj.repr
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (763))
                                          (Prims.of_int (2))
                                          (Prims.of_int (766))
                                          (Prims.of_int (70)))))
                         with
                         | true ->
                             (match match (FStar_Tactics_Derived.cur_env ())
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (763))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (70))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (763))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (763))
                                                              (Prims.of_int (46))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (763))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (763))
                                                        (Prims.of_int (46))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (763))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (763))
                                                          (Prims.of_int (46)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((FStar_Reflection_Builtins.binders_of_env
                                                   a2),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (763))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (763))
                                                             (Prims.of_int (46))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a2, ps'1) ->
                                  Obj.repr
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (764))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (766))
                                                      (Prims.of_int (70)))))
                                     with
                                     | true ->
                                         (match (interp_abspat abspat)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (764))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (70))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (764))
                                                              (Prims.of_int (30))
                                                              (Prims.of_int (764))
                                                              (Prims.of_int (50))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a3, ps'2) ->
                                              Obj.repr
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (764))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (766))
                                                                  (Prims.of_int (70)))))
                                                 with
                                                 | true ->
                                                     ((match a3 with
                                                       | (problem,
                                                          continuation) ->
                                                           (fun ps1 ->
                                                              match Obj.magic
                                                                    ((k
                                                                    continuation)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (70)))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a4, ps'3)
                                                                  ->
                                                                  Obj.repr
                                                                    (
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (70)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (solve_mp
                                                                    problem
                                                                    a2 a1 a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (766))
                                                                    (Prims.of_int (70)))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'3)
                                                                  ->
                                                                  Obj.repr
                                                                    (
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (764))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (766))
                                                                   (Prims.of_int (70)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'2) ->
                                              Obj.repr
                                                (FStar_Tactics_Result.Failed
                                                   (e, ps'2))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  Obj.repr
                                    (FStar_Tactics_Result.Failed (e, ps'1)))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   Obj.magic
                     (Obj.repr (FStar_Tactics_Result.Failed (e, ps'))))
          uu___2 uu___1 uu___
let inspect_abspat_problem :
  'a .
    'a ->
      FStar_Tactics_Types.proofstate ->
        matching_problem FStar_Tactics_Result.__result
  =
  fun abspat ->
    fun ps ->
      match (interp_abspat abspat)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (770)) (Prims.of_int (6))
                          (Prims.of_int (770)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a1, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (770)) (Prims.of_int (2))
                            (Prims.of_int (770)) (Prims.of_int (31)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((FStar_Pervasives_Native.fst a1),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (770)) (Prims.of_int (2))
                               (Prims.of_int (770)) (Prims.of_int (31))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let inspect_abspat_solution :
  'a .
    'a ->
      FStar_Tactics_Types.proofstate ->
        matching_solution FStar_Tactics_Result.__result
  =
  fun abspat ->
    match_abspat abspat
      (fun uu___ ->
         fun s ->
           FStar_Tactics_Result.Success
             ((fun solution ->
                 fun s1 -> FStar_Tactics_Result.Success (solution, s1)), s))
let tpair :
  'a 'b .
    'a ->
      FStar_Tactics_Types.proofstate ->
        ('b ->
           FStar_Tactics_Types.proofstate ->
             ('a * 'b) FStar_Tactics_Result.__result)
          FStar_Tactics_Result.__result
  =
  fun x ->
    fun s ->
      FStar_Tactics_Result.Success
        ((fun y -> fun s1 -> FStar_Tactics_Result.Success ((x, y), s1)), s)
let gpm :
  'b 'a .
    'a ->
      unit ->
        FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun abspat ->
    fun uu___ ->
      fun ps ->
        match (match_abspat abspat tpair)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (794)) (Prims.of_int (31))
                            (Prims.of_int (794)) (Prims.of_int (56))))))
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (794)) (Prims.of_int (2))
                              (Prims.of_int (795)) (Prims.of_int (52)))))
             with
             | true ->
                 ((match a1 with
                   | (continuation, solution) ->
                       (fun ps1 ->
                          match (interp_abspat_continuation continuation)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (795))
                                              (Prims.of_int (2))
                                              (Prims.of_int (795))
                                              (Prims.of_int (52))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (795))
                                                (Prims.of_int (2))
                                                (Prims.of_int (795))
                                                (Prims.of_int (52)))))
                               with
                               | true ->
                                   (a2 solution)
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (795))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (795))
                                                 (Prims.of_int (52)))))))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (794)) (Prims.of_int (2))
                               (Prims.of_int (795)) (Prims.of_int (52)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let pm :
  'b 'a .
    'a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  = fun abspat -> match_abspat abspat interp_abspat_continuation
let fetch_eq_side' :
  'a . unit -> (FStar_Reflection_Types.term * FStar_Reflection_Types.term) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (gpm
            (fun left ->
               fun right ->
                 fun g ->
                   fun ps ->
                     match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (818))
                                            (Prims.of_int (10))
                                            (Prims.of_int (818))
                                            (Prims.of_int (20))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (818)) (Prims.of_int (9))
                                      (Prims.of_int (818))
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
                                                       ps
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (818))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (818))
                                                             (Prims.of_int (20))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (818))
                                                       (Prims.of_int (9))
                                                       (Prims.of_int (818))
                                                       (Prims.of_int (34))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (818))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (818))
                                                 (Prims.of_int (33))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (818))
                                           (Prims.of_int (9))
                                           (Prims.of_int (818))
                                           (Prims.of_int (34)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (((Obj.magic
                                     (failwith
                                        "Cannot evaluate open quotation at runtime")),
                                   (Obj.magic
                                      (failwith
                                         "Cannot evaluate open quotation at runtime"))),
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
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (818))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (818))
                                                                (Prims.of_int (20))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (818))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (818))
                                                          (Prims.of_int (34))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (818))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (818))
                                                    (Prims.of_int (33))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (818))
                                              (Prims.of_int (9))
                                              (Prims.of_int (818))
                                              (Prims.of_int (34))))))))) ()))
      uu___
