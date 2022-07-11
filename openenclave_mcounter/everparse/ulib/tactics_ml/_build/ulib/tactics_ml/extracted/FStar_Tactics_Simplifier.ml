open Prims


let (tiff :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_refl"])))
let (step :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_trans"])))




























let (is_true :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Reflection_Formula.term_as_formula' t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (137)) (Prims.of_int (16))
                          (Prims.of_int (137)) (Prims.of_int (34))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (137)) (Prims.of_int (10))
                            (Prims.of_int (150)) (Prims.of_int (14)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.True_ ->
                     (fun s -> FStar_Tactics_Result.Success (true, s))
                 | uu___ ->
                     (match FStar_Reflection_Builtins.inspect_ln t with
                      | FStar_Reflection_Data.Tv_App (l, r) ->
                          (match FStar_Reflection_Builtins.inspect_ln l with
                           | FStar_Reflection_Data.Tv_Abs (b, t1) ->
                               (fun ps1 ->
                                  match (FStar_Reflection_Formula.term_as_formula'
                                           t1)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Simplifier.fst"
                                                      (Prims.of_int (143))
                                                      (Prims.of_int (28))
                                                      (Prims.of_int (143))
                                                      (Prims.of_int (46))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Simplifier.fst"
                                                        (Prims.of_int (143))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (145))
                                                        (Prims.of_int (28)))))
                                       with
                                       | true ->
                                           ((match a1 with
                                             | FStar_Reflection_Formula.True_
                                                 ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (true, s))
                                             | uu___1 ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (false, s))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Simplifier.fst"
                                                         (Prims.of_int (143))
                                                         (Prims.of_int (22))
                                                         (Prims.of_int (145))
                                                         (Prims.of_int (28)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1))
                           | uu___1 ->
                               (fun s ->
                                  FStar_Tactics_Result.Success (false, s)))
                      | uu___1 ->
                          (fun s -> FStar_Tactics_Result.Success (false, s)))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                             (Prims.of_int (137)) (Prims.of_int (10))
                             (Prims.of_int (150)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (is_false :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Reflection_Formula.term_as_formula' t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (155)) (Prims.of_int (16))
                          (Prims.of_int (155)) (Prims.of_int (34))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (155)) (Prims.of_int (10))
                            (Prims.of_int (168)) (Prims.of_int (14)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.False_ ->
                     (fun s -> FStar_Tactics_Result.Success (true, s))
                 | uu___ ->
                     (match FStar_Reflection_Builtins.inspect_ln t with
                      | FStar_Reflection_Data.Tv_App (l, r) ->
                          (match FStar_Reflection_Builtins.inspect_ln l with
                           | FStar_Reflection_Data.Tv_Abs (b, t1) ->
                               (fun ps1 ->
                                  match (FStar_Reflection_Formula.term_as_formula'
                                           t1)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Simplifier.fst"
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (28))
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (46))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Simplifier.fst"
                                                        (Prims.of_int (161))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (163))
                                                        (Prims.of_int (28)))))
                                       with
                                       | true ->
                                           ((match a1 with
                                             | FStar_Reflection_Formula.False_
                                                 ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (true, s))
                                             | uu___1 ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (false, s))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Simplifier.fst"
                                                         (Prims.of_int (161))
                                                         (Prims.of_int (22))
                                                         (Prims.of_int (163))
                                                         (Prims.of_int (28)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1))
                           | uu___1 ->
                               (fun s ->
                                  FStar_Tactics_Result.Success (false, s)))
                      | uu___1 ->
                          (fun s -> FStar_Tactics_Result.Success (false, s)))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                             (Prims.of_int (155)) (Prims.of_int (10))
                             (Prims.of_int (168)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (inhabit :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (173)) (Prims.of_int (12))
                          (Prims.of_int (173)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (174)) (Prims.of_int (4))
                            (Prims.of_int (181)) (Prims.of_int (18)))))
           with
           | true ->
               ((match FStar_Reflection_Builtins.inspect_ln a with
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun ps1 ->
                        match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Simplifier.fst"
                                               (Prims.of_int (176))
                                               (Prims.of_int (17))
                                               (Prims.of_int (176))
                                               (Prims.of_int (30))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Simplifier.fst"
                                         (Prims.of_int (177))
                                         (Prims.of_int (13))
                                         (Prims.of_int (180))
                                         (Prims.of_int (20)))))
                        with
                        | true ->
                            (if
                               (FStar_Reflection_Builtins.inspect_fv fv) =
                                 FStar_Reflection_Const.int_lid
                             then
                               FStar_Tactics_Derived.exact
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_Const
                                       (FStar_Reflection_Data.C_Int
                                          (Prims.of_int (42)))))
                             else
                               if
                                 (FStar_Reflection_Builtins.inspect_fv fv) =
                                   FStar_Reflection_Const.bool_lid
                               then
                                 FStar_Tactics_Derived.exact
                                   (FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_Const
                                         FStar_Reflection_Data.C_True))
                               else
                                 if
                                   (FStar_Reflection_Builtins.inspect_fv fv)
                                     = FStar_Reflection_Const.unit_lid
                                 then
                                   FStar_Tactics_Derived.exact
                                     (FStar_Reflection_Builtins.pack_ln
                                        (FStar_Reflection_Data.Tv_Const
                                           FStar_Reflection_Data.C_Unit))
                                 else FStar_Tactics_Derived.fail "")
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (176))
                                                (Prims.of_int (17))
                                                (Prims.of_int (176))
                                                (Prims.of_int (30))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (177))
                                          (Prims.of_int (13))
                                          (Prims.of_int (180))
                                          (Prims.of_int (20)))))))
                 | uu___1 -> FStar_Tactics_Derived.fail ""))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                             (Prims.of_int (174)) (Prims.of_int (4))
                             (Prims.of_int (181)) (Prims.of_int (18)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (simplify_point :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (recurse ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (188)) (Prims.of_int (4))
                          (Prims.of_int (188)) (Prims.of_int (14))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (189)) (Prims.of_int (4))
                            (Prims.of_int (245)) (Prims.of_int (81)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.norm [])
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (189))
                                          (Prims.of_int (4))
                                          (Prims.of_int (245))
                                          (Prims.of_int (81))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Simplifier.fst"
                                    (Prims.of_int (189)) (Prims.of_int (4))
                                    (Prims.of_int (189)) (Prims.of_int (11))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Simplifier.fst"
                                      (Prims.of_int (190)) (Prims.of_int (4))
                                      (Prims.of_int (245))
                                      (Prims.of_int (81)))))
                     with
                     | true ->
                         (match (FStar_Tactics_Derived.cur_goal ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Simplifier.fst"
                                                    (Prims.of_int (190))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (245))
                                                    (Prims.of_int (81))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Simplifier.fst"
                                              (Prims.of_int (190))
                                              (Prims.of_int (12))
                                              (Prims.of_int (190))
                                              (Prims.of_int (23))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (191))
                                                (Prims.of_int (4))
                                                (Prims.of_int (245))
                                                (Prims.of_int (81)))))
                               with
                               | true ->
                                   (match (FStar_Reflection_Formula.term_as_formula
                                             a2)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Simplifier.fst"
                                                              (Prims.of_int (191))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (245))
                                                              (Prims.of_int (81))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Simplifier.fst"
                                                        (Prims.of_int (191))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (191))
                                                        (Prims.of_int (29))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'3)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'3
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Simplifier.fst"
                                                          (Prims.of_int (194))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (245))
                                                          (Prims.of_int (81)))))
                                         with
                                         | true ->
                                             ((match a3 with
                                               | FStar_Reflection_Formula.Iff
                                                   (l, r) ->
                                                   (fun ps1 ->
                                                      match (FStar_Reflection_Formula.term_as_formula'
                                                               l)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (38))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))
                                                           with
                                                           | true ->
                                                               ((match a4
                                                                 with
                                                                 | FStar_Reflection_Formula.And
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (198))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_and_p"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (199))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_true"])))
                                                                    else
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a7
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_and_p"])))
                                                                    else
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,
                                                                    ps'8) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a8
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_false"])))
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Or
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (205))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_or_p"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (206))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_true"])))
                                                                    else
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a7
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_or_p"])))
                                                                    else
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,
                                                                    ps'8) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a8
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_false"])))
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Implies
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (212))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_imp_p"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (213))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_imp_true"])))
                                                                    else
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a7
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_imp_p"])))
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Forall
                                                                    (b, p) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (218))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_true"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (30))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_false"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (82))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (94)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (inhabit
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (94)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7))
                                                                    tiff
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Exists
                                                                    (b, p) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (30))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_false"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (30))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_true"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (81))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (93)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (inhabit
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (93)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7))
                                                                    tiff
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Not
                                                                    p ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_true"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (30))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_false"])))
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Iff
                                                                    (p, q) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (step ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (19))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (is_true
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (236))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a6
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_iff_p"])))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (is_true
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (29))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,
                                                                    ps'7) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a7
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_true"])))
                                                                    else
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,
                                                                    ps'8) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a8
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_iff_p"])))
                                                                    else
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (is_false
                                                                    q)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (30))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a9,
                                                                    ps'9) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a9
                                                                    then
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_false"])))
                                                                    else
                                                                    tiff ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (24)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (simplify_point
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (29)))))))
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
                                                                    (e, ps'5))
                                                                 | uu___1 ->
                                                                    tiff ()))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4))
                                               | uu___1 ->
                                                   FStar_Tactics_Derived.fail
                                                     "simplify_point: failed precondition: goal should be `g <==> ?u`"))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'3
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Simplifier.fst"
                                                           (Prims.of_int (194))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (245))
                                                           (Prims.of_int (81)))))))
                                    | FStar_Tactics_Result.Failed (e, ps'3)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'3)))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
and (recurse :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (step ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (249)) (Prims.of_int (4))
                          (Prims.of_int (249)) (Prims.of_int (11))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (250)) (Prims.of_int (4))
                            (Prims.of_int (286)) (Prims.of_int (74)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.norm [])
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (250))
                                          (Prims.of_int (4))
                                          (Prims.of_int (286))
                                          (Prims.of_int (74))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Simplifier.fst"
                                    (Prims.of_int (250)) (Prims.of_int (4))
                                    (Prims.of_int (250)) (Prims.of_int (11))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Simplifier.fst"
                                      (Prims.of_int (251)) (Prims.of_int (4))
                                      (Prims.of_int (286))
                                      (Prims.of_int (74)))))
                     with
                     | true ->
                         (match (FStar_Tactics_Derived.cur_goal ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Simplifier.fst"
                                                    (Prims.of_int (251))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (286))
                                                    (Prims.of_int (74))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Simplifier.fst"
                                              (Prims.of_int (251))
                                              (Prims.of_int (12))
                                              (Prims.of_int (251))
                                              (Prims.of_int (23))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (252))
                                                (Prims.of_int (4))
                                                (Prims.of_int (286))
                                                (Prims.of_int (74)))))
                               with
                               | true ->
                                   (match (FStar_Reflection_Formula.term_as_formula
                                             a2)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Simplifier.fst"
                                                              (Prims.of_int (252))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (286))
                                                              (Prims.of_int (74))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Simplifier.fst"
                                                        (Prims.of_int (252))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (252))
                                                        (Prims.of_int (29))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'3)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'3
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Simplifier.fst"
                                                          (Prims.of_int (255))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (286))
                                                          (Prims.of_int (74)))))
                                         with
                                         | true ->
                                             ((match a3 with
                                               | FStar_Reflection_Formula.Iff
                                                   (l, r) ->
                                                   (fun ps1 ->
                                                      match (FStar_Reflection_Formula.term_as_formula'
                                                               l)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (38))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (22)))))
                                                           with
                                                           | true ->
                                                               ((match a4
                                                                 with
                                                                 | FStar_Reflection_Formula.And
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "and_cong"]))))
                                                                    simplify_point
                                                                 | FStar_Reflection_Formula.Or
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "or_cong"]))))
                                                                    simplify_point
                                                                 | FStar_Reflection_Formula.Implies
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "imp_cong"]))))
                                                                    simplify_point
                                                                 | FStar_Reflection_Formula.Forall
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "fa_cong"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.intro
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (28))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (simplify_point
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (29)))))))
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
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Exists
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "ex_cong"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.intro
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (28))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (simplify_point
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (29)))))))
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
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Not
                                                                    uu___1 ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "neg_cong"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (35))))))
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
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (simplify_point
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (29)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                 | FStar_Reflection_Formula.Iff
                                                                    (uu___1,
                                                                    uu___2)
                                                                    ->
                                                                    FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "iff_cong"]))))
                                                                    simplify_point
                                                                 | uu___1 ->
                                                                    tiff ()))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (22)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4))
                                               | uu___1 ->
                                                   FStar_Tactics_Derived.fail
                                                     "recurse: failed precondition: goal should be `g <==> ?u`"))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'3
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Simplifier.fst"
                                                           (Prims.of_int (255))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (286))
                                                           (Prims.of_int (74)))))))
                                    | FStar_Tactics_Result.Failed (e, ps'3)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'3)))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (simplify :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Simplifier"; "equiv"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (292)) (Prims.of_int (4))
                          (Prims.of_int (292)) (Prims.of_int (24))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                            (Prims.of_int (293)) (Prims.of_int (4))
                            (Prims.of_int (293)) (Prims.of_int (21)))))
           with
           | true ->
               (simplify_point ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                             (Prims.of_int (293)) (Prims.of_int (4))
                             (Prims.of_int (293)) (Prims.of_int (21)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')