open Prims
let (cur_formula :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Formula.formula FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (25)) (Prims.of_int (51))
                          (Prims.of_int (25)) (Prims.of_int (64))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (25)) (Prims.of_int (35))
                            (Prims.of_int (25)) (Prims.of_int (64)))))
           with
           | true ->
               (FStar_Reflection_Formula.term_as_formula a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (25)) (Prims.of_int (35))
                             (Prims.of_int (25)) (Prims.of_int (64)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (l_revert :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.revert ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (33)) (Prims.of_int (4))
                          (Prims.of_int (33)) (Prims.of_int (13))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (34)) (Prims.of_int (4))
                            (Prims.of_int (34)) (Prims.of_int (26)))))
           with
           | true ->
               (FStar_Tactics_Derived.apply
                  (FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Logic"; "revert_squash"]))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (34)) (Prims.of_int (4))
                             (Prims.of_int (34)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (l_revert_all :
  FStar_Reflection_Types.binders ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun bs ->
    match bs with
    | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
    | uu___::tl ->
        (fun ps ->
           match (l_revert ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (39)) (Prims.of_int (21))
                               (Prims.of_int (39)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Logic.fst"
                                 (Prims.of_int (39)) (Prims.of_int (34))
                                 (Prims.of_int (39)) (Prims.of_int (49)))))
                with
                | true ->
                    (l_revert_all tl)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (39)) (Prims.of_int (34))
                                  (Prims.of_int (39)) (Prims.of_int (49)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))

let (forall_intro :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (46)) (Prims.of_int (4))
                          (Prims.of_int (46)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (47)) (Prims.of_int (4))
                            (Prims.of_int (47)) (Prims.of_int (12)))))
           with
           | true ->
               (FStar_Tactics_Builtins.intro ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (47)) (Prims.of_int (4))
                             (Prims.of_int (47)) (Prims.of_int (12)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (forall_intro_as :
  Prims.string ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun s ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (50)) (Prims.of_int (4))
                          (Prims.of_int (50)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (51)) (Prims.of_int (4))
                            (Prims.of_int (51)) (Prims.of_int (14)))))
           with
           | true ->
               (FStar_Tactics_Derived.intro_as s)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (51)) (Prims.of_int (4))
                             (Prims.of_int (51)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (forall_intros :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binders FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.repeat1 forall_intro

let (split :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.try_with
      (fun uu___1 ->
         match () with
         | () ->
             FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "split_lem"]))))
      (fun uu___1 -> FStar_Tactics_Derived.fail "Could not split goal")

let (implies_intro :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (70)) (Prims.of_int (4))
                          (Prims.of_int (70)) (Prims.of_int (32))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (71)) (Prims.of_int (4))
                            (Prims.of_int (71)) (Prims.of_int (12)))))
           with
           | true ->
               (FStar_Tactics_Builtins.intro ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (71)) (Prims.of_int (4))
                             (Prims.of_int (71)) (Prims.of_int (12)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (implies_intros :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binders FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.repeat1 implies_intro
let (l_intro :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.or_else forall_intro implies_intro
let (l_intros :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder Prims.list FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.repeat l_intro
let (mintro :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.first
      [FStar_Tactics_Builtins.intro;
      implies_intro;
      forall_intro;
      (fun uu___1 -> FStar_Tactics_Derived.fail "cannot intro")]
let (mintros :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder Prims.list FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Derived.repeat mintro
let (squash_intro :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Squash"; "return_squash"])))
let (l_exact :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ -> match () with | () -> FStar_Tactics_Derived.exact t)
      (fun uu___ ->
         fun ps ->
           match (squash_intro ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (91)) (Prims.of_int (12))
                               (Prims.of_int (91)) (Prims.of_int (27))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Logic.fst"
                                 (Prims.of_int (91)) (Prims.of_int (29))
                                 (Prims.of_int (91)) (Prims.of_int (36)))))
                with
                | true ->
                    (FStar_Tactics_Derived.exact t)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (91)) (Prims.of_int (29))
                                  (Prims.of_int (91)) (Prims.of_int (36)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (hyp :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ps ->
      match (FStar_Tactics_Derived.binder_to_term b)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (93)) (Prims.of_int (40))
                          (Prims.of_int (93)) (Prims.of_int (58))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (93)) (Prims.of_int (32))
                            (Prims.of_int (93)) (Prims.of_int (58)))))
           with
           | true ->
               (l_exact a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (93)) (Prims.of_int (32))
                             (Prims.of_int (93)) (Prims.of_int (58)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (pose_lemma :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match match (FStar_Tactics_Derived.cur_env ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (100))
                                      (Prims.of_int (10))
                                      (Prims.of_int (100))
                                      (Prims.of_int (28))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Logic.fst"
                                (Prims.of_int (100)) (Prims.of_int (14))
                                (Prims.of_int (100)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (100)) (Prims.of_int (10))
                                  (Prims.of_int (100)) (Prims.of_int (28)))))
                 with
                 | true ->
                     (FStar_Tactics_Builtins.tcc a t)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Logic.fst"
                                   (Prims.of_int (100)) (Prims.of_int (10))
                                   (Prims.of_int (100)) (Prims.of_int (28)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (101)) (Prims.of_int (2))
                            (Prims.of_int (118)) (Prims.of_int (5)))))
           with
           | true ->
               (match (match FStar_Reflection_Builtins.inspect_comp a with
                       | FStar_Reflection_Data.C_Lemma (pre, post, uu___) ->
                           (fun s ->
                              FStar_Tactics_Result.Success ((pre, post), s))
                       | uu___ -> FStar_Tactics_Derived.fail "")
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (2))
                                          (Prims.of_int (118))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (102)) (Prims.of_int (4))
                                    (Prims.of_int (104)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (101)) (Prims.of_int (2))
                                      (Prims.of_int (118)) (Prims.of_int (5)))))
                     with
                     | true ->
                         ((match a1 with
                           | (pre, post) ->
                               (fun ps1 ->
                                  match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (106))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (106))
                                                         (Prims.of_int (27))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (118))
                                                   (Prims.of_int (5)))))
                                  with
                                  | true ->
                                      (match (FStar_Tactics_Derived.norm_term
                                                []
                                                (FStar_Reflection_Builtins.pack_ln
                                                   (FStar_Reflection_Data.Tv_App
                                                      (post,
                                                        ((FStar_Reflection_Builtins.pack_ln
                                                            (FStar_Reflection_Data.Tv_Const
                                                               FStar_Reflection_Data.C_Unit)),
                                                          FStar_Reflection_Data.Q_Explicit)))))
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps1
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (27))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (107))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (118))
                                                                 (Prims.of_int (5))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Logic.fst"
                                                           (Prims.of_int (107))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (107))
                                                           (Prims.of_int (30))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a2, ps'2) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Logic.fst"
                                                             (Prims.of_int (109))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (118))
                                                             (Prims.of_int (5)))))
                                            with
                                            | true ->
                                                (match (FStar_Reflection_Formula.term_as_formula'
                                                          pre)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (28))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a3, ps'3) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5)))))
                                                      with
                                                      | true ->
                                                          ((match a3 with
                                                            | FStar_Reflection_Formula.True_
                                                                ->
                                                                FStar_Tactics_Derived.pose
                                                                  (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (a2,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Builtins.pack_binder
                                                                    (FStar_Reflection_Builtins.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    = "uu___";
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (93));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    })
                                                                    FStar_Reflection_Data.Q_Explicit
                                                                    []), t))),
                                                                    FStar_Reflection_Data.Q_Explicit))))
                                                            | uu___ ->
                                                                (fun ps2 ->
                                                                   match 
                                                                    (FStar_Tactics_Derived.tcut
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (98))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    a4)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (98))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (81))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (a2,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (a5,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Builtins.pack_binder
                                                                    (FStar_Reflection_Builtins.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    = "uu___";
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (100));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    })
                                                                    FStar_Reflection_Data.Q_Explicit
                                                                    []), t))),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Derived.pose
                                                                    a5)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (102)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.flip
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (11))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (FStar_Tactics_Derived.trytac
                                                                    FStar_Tactics_Derived.trivial)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (27))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (27))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (27)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (27))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
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
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Effect.fsti"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (19))))))))
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
                                                                    (e, ps'6)))
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
                                                                    (e, ps'4))))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (5)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3)))
                                       | FStar_Tactics_Result.Failed
                                           (e, ps'2) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'2)))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                                       (Prims.of_int (101))
                                       (Prims.of_int (2))
                                       (Prims.of_int (118))
                                       (Prims.of_int (5)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (explode :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.repeatseq
               (fun uu___1 ->
                  FStar_Tactics_Derived.first
                    [(fun uu___2 ->
                        fun ps1 ->
                          match (l_intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (122))
                                              (Prims.of_int (50))
                                              (Prims.of_int (122))
                                              (Prims.of_int (62))))))
                          with
                          | FStar_Tactics_Result.Success (a, ps') ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (122))
                                                (Prims.of_int (43))
                                                (Prims.of_int (122))
                                                (Prims.of_int (62)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (122))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (122))
                                                   (Prims.of_int (62))))))))
                          | FStar_Tactics_Result.Failed (e, ps') ->
                              FStar_Tactics_Result.Failed (e, ps'));
                    (fun uu___2 ->
                       fun ps1 ->
                         match (split ())
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Logic.fst"
                                             (Prims.of_int (123))
                                             (Prims.of_int (50))
                                             (Prims.of_int (123))
                                             (Prims.of_int (60))))))
                         with
                         | FStar_Tactics_Result.Success (a, ps') ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (123))
                                               (Prims.of_int (43))
                                               (Prims.of_int (123))
                                               (Prims.of_int (60)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    ((),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Logic.fst"
                                                  (Prims.of_int (123))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (123))
                                                  (Prims.of_int (60))))))))
                         | FStar_Tactics_Result.Failed (e, ps') ->
                             FStar_Tactics_Result.Failed (e, ps'))]))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (121)) (Prims.of_int (11))
                          (Prims.of_int (123)) (Prims.of_int (64))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (121)) (Prims.of_int (4))
                            (Prims.of_int (123)) (Prims.of_int (64)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (121)) (Prims.of_int (4))
                               (Prims.of_int (123)) (Prims.of_int (64))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (visit :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun callback ->
    FStar_Tactics_Derived.focus
      (fun uu___ ->
         FStar_Tactics_Derived.or_else callback
           (fun uu___1 ->
              fun ps ->
                match (FStar_Tactics_Derived.cur_goal ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (129)) (Prims.of_int (28))
                                    (Prims.of_int (129)) (Prims.of_int (39))))))
                with
                | FStar_Tactics_Result.Success (a, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (130))
                                      (Prims.of_int (20))
                                      (Prims.of_int (140))
                                      (Prims.of_int (26)))))
                     with
                     | true ->
                         (match (FStar_Reflection_Formula.term_as_formula a)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (130))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (140))
                                                    (Prims.of_int (26))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (130))
                                              (Prims.of_int (26))
                                              (Prims.of_int (130))
                                              (Prims.of_int (43))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (130))
                                                (Prims.of_int (20))
                                                (Prims.of_int (140))
                                                (Prims.of_int (26)))))
                               with
                               | true ->
                                   ((match a1 with
                                     | FStar_Reflection_Formula.Forall
                                         (b, phi) ->
                                         (fun ps1 ->
                                            match (forall_intros ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (132))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (132))
                                                                (Prims.of_int (54))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2, ps'2) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Logic.fst"
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (24))
                                                                  (Prims.of_int (133))
                                                                  (Prims.of_int (87)))))
                                                 with
                                                 | true ->
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu___2 ->
                                                           visit callback)
                                                        (fun uu___2 ->
                                                           l_revert_all a2))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (24))
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (87)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'2) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'2))
                                     | FStar_Reflection_Formula.And (p, q) ->
                                         FStar_Tactics_Derived.seq split
                                           (fun uu___2 -> visit callback)
                                     | FStar_Reflection_Formula.Implies
                                         (p, q) ->
                                         (fun ps1 ->
                                            match (implies_intro ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (137))
                                                                (Prims.of_int (32))
                                                                (Prims.of_int (137))
                                                                (Prims.of_int (48))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2, ps'2) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Logic.fst"
                                                                  (Prims.of_int (138))
                                                                  (Prims.of_int (24))
                                                                  (Prims.of_int (138))
                                                                  (Prims.of_int (63)))))
                                                 with
                                                 | true ->
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu___2 ->
                                                           visit callback)
                                                        l_revert)
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (138))
                                                                   (Prims.of_int (24))
                                                                   (Prims.of_int (138))
                                                                   (Prims.of_int (63)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'2) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'2))
                                     | uu___2 ->
                                         (fun s ->
                                            FStar_Tactics_Result.Success
                                              ((), s))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (130))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (140))
                                                 (Prims.of_int (26)))))))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
let rec (simplify_eq_implication :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (145)) (Prims.of_int (12))
                          (Prims.of_int (145)) (Prims.of_int (22))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (146)) (Prims.of_int (4))
                            (Prims.of_int (155)) (Prims.of_int (37)))))
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
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (146))
                                          (Prims.of_int (4))
                                          (Prims.of_int (155))
                                          (Prims.of_int (37))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (146)) (Prims.of_int (12))
                                    (Prims.of_int (146)) (Prims.of_int (23))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (147)) (Prims.of_int (4))
                                      (Prims.of_int (155))
                                      (Prims.of_int (37)))))
                     with
                     | true ->
                         (match (FStar_Tactics_Derived.destruct_equality_implication
                                   a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (147))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (155))
                                                    (Prims.of_int (37))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (147))
                                              (Prims.of_int (12))
                                              (Prims.of_int (147))
                                              (Prims.of_int (43))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (148))
                                                (Prims.of_int (4))
                                                (Prims.of_int (155))
                                                (Prims.of_int (37)))))
                               with
                               | true ->
                                   ((match a2 with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Tactics_Derived.fail
                                           "Not an equality implication"
                                     | FStar_Pervasives_Native.Some
                                         (uu___1, rhs) ->
                                         (fun ps1 ->
                                            match (implies_intro ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (152))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (152))
                                                                (Prims.of_int (35))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Logic.fst"
                                                                  (Prims.of_int (153))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (155))
                                                                  (Prims.of_int (37)))))
                                                 with
                                                 | true ->
                                                     (match (FStar_Tactics_Builtins.rewrite
                                                               a3)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (37))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (20))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (37)))))
                                                           with
                                                           | true ->
                                                               (match 
                                                                  (FStar_Tactics_Builtins.clear_top
                                                                    ())
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (37))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (20))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (37)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (visit
                                                                    simplify_eq_implication)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (37)))))))
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
                                                  (e, ps'3))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (148))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (155))
                                                 (Prims.of_int (37)))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (rewrite_all_equalities :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> visit simplify_eq_implication
let rec (unfold_definition_and_simplify_eq :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (161)) (Prims.of_int (12))
                          (Prims.of_int (161)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (162)) (Prims.of_int (4))
                            (Prims.of_int (176)) (Prims.of_int (11)))))
           with
           | true ->
               (match (FStar_Reflection_Formula.term_as_formula a)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (162))
                                          (Prims.of_int (4))
                                          (Prims.of_int (176))
                                          (Prims.of_int (11))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (162)) (Prims.of_int (10))
                                    (Prims.of_int (162)) (Prims.of_int (27))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (162)) (Prims.of_int (4))
                                      (Prims.of_int (176))
                                      (Prims.of_int (11)))))
                     with
                     | true ->
                         ((match a1 with
                           | FStar_Reflection_Formula.App (hd, arg) ->
                               if FStar_Reflection_Builtins.term_eq hd tm
                               then FStar_Tactics_Derived.trivial ()
                               else
                                 (fun s ->
                                    FStar_Tactics_Result.Success ((), s))
                           | uu___ ->
                               (fun ps1 ->
                                  match (FStar_Tactics_Derived.destruct_equality_implication
                                           a)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Logic.fst"
                                                      (Prims.of_int (168))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (168))
                                                      (Prims.of_int (47))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Logic.fst"
                                                        (Prims.of_int (169))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (175))
                                                        (Prims.of_int (66)))))
                                       with
                                       | true ->
                                           ((match a2 with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Tactics_Derived.fail
                                                   "Not an equality implication"
                                             | FStar_Pervasives_Native.Some
                                                 (uu___1, rhs) ->
                                                 (fun ps2 ->
                                                    match (implies_intro ())
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (39))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a3, ps'3) ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66)))))
                                                         with
                                                         | true ->
                                                             (match (FStar_Tactics_Builtins.rewrite
                                                                    a3)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (24))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.clear_top
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (24))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (visit
                                                                    (fun
                                                                    uu___2 ->
                                                                    unfold_definition_and_simplify_eq
                                                                    tm))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (66)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'4)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                    | FStar_Tactics_Result.Failed
                                                        (e, ps'3) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps'3))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (169))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (66)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                                       (Prims.of_int (162))
                                       (Prims.of_int (4))
                                       (Prims.of_int (176))
                                       (Prims.of_int (11)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (unsquash :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (182)) (Prims.of_int (12))
                             (Prims.of_int (182)) (Prims.of_int (18))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                       (Prims.of_int (183)) (Prims.of_int (4))
                       (Prims.of_int (185)) (Prims.of_int (37)))))
      with
      | true ->
          (match (FStar_Tactics_Derived.apply_lemma
                    (FStar_Reflection_Derived.mk_e_app
                       (FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_FVar
                             (FStar_Reflection_Builtins.pack_fv
                                ["FStar"; "Tactics"; "Logic"; "vbind"]))) 
                       [t]))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Logic.fst"
                                           (Prims.of_int (182))
                                           (Prims.of_int (12))
                                           (Prims.of_int (182))
                                           (Prims.of_int (18))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (183)) (Prims.of_int (4))
                                     (Prims.of_int (185)) (Prims.of_int (37))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (183)) (Prims.of_int (4))
                               (Prims.of_int (183)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Logic.fst"
                                 (Prims.of_int (184)) (Prims.of_int (4))
                                 (Prims.of_int (185)) (Prims.of_int (37)))))
                with
                | true ->
                    (match (FStar_Tactics_Builtins.intro ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (184))
                                               (Prims.of_int (4))
                                               (Prims.of_int (185))
                                               (Prims.of_int (37))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Logic.fst"
                                         (Prims.of_int (184))
                                         (Prims.of_int (12))
                                         (Prims.of_int (184))
                                         (Prims.of_int (20))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Logic.fst"
                                           (Prims.of_int (185))
                                           (Prims.of_int (4))
                                           (Prims.of_int (185))
                                           (Prims.of_int (37)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_Var
                                       (FStar_Reflection_Derived.bv_of_binder
                                          a1))),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (185))
                                              (Prims.of_int (4))
                                              (Prims.of_int (185))
                                              (Prims.of_int (37))))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))

let (cases_or :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun o ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv
                  ["FStar"; "Tactics"; "Logic"; "or_ind"]))) [o])

let (cases_bool :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (203)) (Prims.of_int (13))
                             (Prims.of_int (203)) (Prims.of_int (22))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                       (Prims.of_int (204)) (Prims.of_int (4))
                       (Prims.of_int (205)) (Prims.of_int (104)))))
      with
      | true ->
          (FStar_Tactics_Derived.seq
             (fun uu___ ->
                FStar_Tactics_Derived.apply_lemma
                  (FStar_Reflection_Derived.mk_e_app
                     (FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar"; "Tactics"; "Logic"; "bool_ind"])))
                     [b]))
             (fun uu___ ->
                fun ps1 ->
                  match (FStar_Tactics_Derived.trytac
                           (fun uu___1 ->
                              fun ps2 ->
                                match (implies_intro ())
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps2
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (205))
                                                    (Prims.of_int (53))
                                                    (Prims.of_int (205))
                                                    (Prims.of_int (69))))))
                                with
                                | FStar_Tactics_Result.Success (a, ps') ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Logic.fst"
                                                      (Prims.of_int (205))
                                                      (Prims.of_int (73))
                                                      (Prims.of_int (205))
                                                      (Prims.of_int (96)))))
                                     with
                                     | true ->
                                         (match (FStar_Tactics_Builtins.rewrite
                                                   a)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (96))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Logic.fst"
                                                              (Prims.of_int (205))
                                                              (Prims.of_int (73))
                                                              (Prims.of_int (205))
                                                              (Prims.of_int (82))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a1, ps'1) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (205))
                                                                (Prims.of_int (84))
                                                                (Prims.of_int (205))
                                                                (Prims.of_int (96)))))
                                               with
                                               | true ->
                                                   (FStar_Tactics_Builtins.clear_top
                                                      ())
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (205))
                                                                 (Prims.of_int (84))
                                                                 (Prims.of_int (205))
                                                                 (Prims.of_int (96)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'1) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'1)))
                                | FStar_Tactics_Result.Failed (e, ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (205))
                                      (Prims.of_int (27))
                                      (Prims.of_int (205))
                                      (Prims.of_int (97))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Logic.fst"
                                        (Prims.of_int (205))
                                        (Prims.of_int (101))
                                        (Prims.of_int (205))
                                        (Prims.of_int (103)))))
                       with
                       | true ->
                           FStar_Tactics_Result.Success
                             ((),
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Logic.fst"
                                           (Prims.of_int (205))
                                           (Prims.of_int (101))
                                           (Prims.of_int (205))
                                           (Prims.of_int (103))))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Logic.fst"
                              (Prims.of_int (203)) (Prims.of_int (13))
                              (Prims.of_int (203)) (Prims.of_int (22))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Logic.fst"
                        (Prims.of_int (204)) (Prims.of_int (4))
                        (Prims.of_int (205)) (Prims.of_int (104))))))


let (left :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_1"])))
let (right :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_2"])))


let (and_elim :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Builtins.pack_fv
                               ["FStar"; "Tactics"; "Logic"; "__and_elim"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_Derived.apply_lemma
           (FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Logic"; "__and_elim'"]))),
                   (t, FStar_Reflection_Data.Q_Explicit)))))
let (destruct_and :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binder * FStar_Reflection_Types.binder)
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (and_elim t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (238)) (Prims.of_int (4))
                          (Prims.of_int (238)) (Prims.of_int (14))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (239)) (Prims.of_int (4))
                            (Prims.of_int (239)) (Prims.of_int (40)))))
           with
           | true ->
               (match (implies_intro ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (239))
                                          (Prims.of_int (4))
                                          (Prims.of_int (239))
                                          (Prims.of_int (40))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (239)) (Prims.of_int (5))
                                    (Prims.of_int (239)) (Prims.of_int (21))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (239)) (Prims.of_int (4))
                                      (Prims.of_int (239))
                                      (Prims.of_int (40)))))
                     with
                     | true ->
                         (match (implies_intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (239))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (239))
                                                    (Prims.of_int (40))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (239))
                                              (Prims.of_int (23))
                                              (Prims.of_int (239))
                                              (Prims.of_int (39))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (239))
                                                (Prims.of_int (4))
                                                (Prims.of_int (239))
                                                (Prims.of_int (40)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((a1, a2),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (239))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (239))
                                                   (Prims.of_int (40))))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (witness :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_raw
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "__witness"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (245)) (Prims.of_int (4))
                          (Prims.of_int (245)) (Prims.of_int (26))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (246)) (Prims.of_int (4))
                            (Prims.of_int (246)) (Prims.of_int (11)))))
           with
           | true ->
               (FStar_Tactics_Derived.exact t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (246)) (Prims.of_int (4))
                             (Prims.of_int (246)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (elim_exists :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binder * FStar_Reflection_Types.binder)
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Logic";
                               "__elim_exists'"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (255)) (Prims.of_int (2))
                          (Prims.of_int (255)) (Prims.of_int (41))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (256)) (Prims.of_int (2))
                            (Prims.of_int (258)) (Prims.of_int (9)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.intro ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (256))
                                          (Prims.of_int (2))
                                          (Prims.of_int (258))
                                          (Prims.of_int (9))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (256)) (Prims.of_int (10))
                                    (Prims.of_int (256)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (257)) (Prims.of_int (2))
                                      (Prims.of_int (258)) (Prims.of_int (9)))))
                     with
                     | true ->
                         (match (FStar_Tactics_Builtins.intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (257))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (258))
                                                    (Prims.of_int (9))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (257))
                                              (Prims.of_int (11))
                                              (Prims.of_int (257))
                                              (Prims.of_int (19))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (258))
                                                (Prims.of_int (2))
                                                (Prims.of_int (258))
                                                (Prims.of_int (9)))))
                               with
                               | true ->
                                   FStar_Tactics_Result.Success
                                     ((a1, a2),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (258))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (258))
                                                   (Prims.of_int (9))))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')


let (instantiate :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun fa ->
    fun x ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               FStar_Tactics_Derived.pose
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_App
                       ((FStar_Reflection_Builtins.pack_ln
                           (FStar_Reflection_Data.Tv_App
                              ((FStar_Reflection_Builtins.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Logic";
                                        "__forall_inst_sq"]))),
                                (fa, FStar_Reflection_Data.Q_Explicit)))),
                         (x, FStar_Reflection_Data.Q_Explicit)))))
        (fun uu___ ->
           FStar_Tactics_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Derived.pose
                      (FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_App
                            ((FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_App
                                   ((FStar_Reflection_Builtins.pack_ln
                                       (FStar_Reflection_Data.Tv_FVar
                                          (FStar_Reflection_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "Logic";
                                             "__forall_inst"]))),
                                     (fa, FStar_Reflection_Data.Q_Explicit)))),
                              (x, FStar_Reflection_Data.Q_Explicit)))))
             (fun uu___1 ->
                FStar_Tactics_Derived.fail "could not instantiate"))

let rec (sk_binder' :
  FStar_Reflection_Types.binders ->
    FStar_Reflection_Types.binder ->
      FStar_Tactics_Types.proofstate ->
        (FStar_Reflection_Types.binders * FStar_Reflection_Types.binder)
          FStar_Tactics_Result.__result)
  =
  fun acc ->
    fun b ->
      FStar_Tactics_Derived.focus
        (fun uu___ ->
           FStar_Tactics_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    (fun ps ->
                       match match match (FStar_Tactics_Derived.binder_to_term
                                            b)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (283))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (283))
                                                                   (Prims.of_int (52))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Logic.fst"
                                                             (Prims.of_int (283))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (283))
                                                             (Prims.of_int (52))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Logic.fst"
                                                       (Prims.of_int (283))
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (283))
                                                       (Prims.of_int (49))))))
                                   with
                                   | FStar_Tactics_Result.Success (a, ps') ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (283))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (283))
                                                         (Prims.of_int (52)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((FStar_Reflection_Builtins.pack_ln
                                                  (FStar_Reflection_Data.Tv_App
                                                     ((FStar_Reflection_Builtins.pack_ln
                                                         (FStar_Reflection_Data.Tv_FVar
                                                            (FStar_Reflection_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "Logic";
                                                               "sklem0"]))),
                                                       (a,
                                                         FStar_Reflection_Data.Q_Explicit)))),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Logic.fst"
                                                            (Prims.of_int (283))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (283))
                                                            (Prims.of_int (52))))))))
                                   | FStar_Tactics_Result.Failed (e, ps') ->
                                       FStar_Tactics_Result.Failed (e, ps')
                             with
                             | FStar_Tactics_Result.Success (a, ps') ->
                                 (match FStar_Tactics_Types.tracepoint
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (283))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (283))
                                                   (Prims.of_int (52)))))
                                  with
                                  | true ->
                                      (FStar_Tactics_Derived.apply_lemma a)
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (283))
                                                    (Prims.of_int (52)))))))
                             | FStar_Tactics_Result.Failed (e, ps') ->
                                 FStar_Tactics_Result.Failed (e, ps')
                       with
                       | FStar_Tactics_Result.Success (a, ps') ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Logic.fst"
                                             (Prims.of_int (284))
                                             (Prims.of_int (6))
                                             (Prims.of_int (288))
                                             (Prims.of_int (29)))))
                            with
                            | true ->
                                (match match match (FStar_Tactics_Derived.ngoals
                                                      ())
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (38))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (23))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (284))
                                                                 (Prims.of_int (9))
                                                                 (Prims.of_int (284))
                                                                 (Prims.of_int (18))))))
                                             with
                                             | FStar_Tactics_Result.Success
                                                 (a1, ps'1) ->
                                                 (match FStar_Tactics_Types.tracepoint
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (284))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (284))
                                                                   (Prims.of_int (23)))))
                                                  with
                                                  | true ->
                                                      FStar_Tactics_Result.Success
                                                        ((a1 <> Prims.int_one),
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'1
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (23))))))))
                                             | FStar_Tactics_Result.Failed
                                                 (e, ps'1) ->
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
                                                             "FStar.Tactics.Logic.fst"
                                                             (Prims.of_int (284))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (284))
                                                             (Prims.of_int (38)))))
                                            with
                                            | true ->
                                                (if a1
                                                 then
                                                   FStar_Tactics_Derived.fail
                                                     "no"
                                                 else
                                                   (fun s ->
                                                      FStar_Tactics_Result.Success
                                                        ((), s)))
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Logic.fst"
                                                              (Prims.of_int (284))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (284))
                                                              (Prims.of_int (38)))))))
                                       | FStar_Tactics_Result.Failed
                                           (e, ps'1) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'1)
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Logic.fst"
                                                       (Prims.of_int (285))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (288))
                                                       (Prims.of_int (29)))))
                                      with
                                      | true ->
                                          (match (FStar_Tactics_Builtins.clear
                                                    b)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Logic.fst"
                                                               (Prims.of_int (285))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (285))
                                                               (Prims.of_int (13))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a2, ps'2) ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (286))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (288))
                                                                 (Prims.of_int (29)))))
                                                with
                                                | true ->
                                                    (match (forall_intro ())
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (30))))))
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a3, ps'3) ->
                                                         (match FStar_Tactics_Types.tracepoint
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29)))))
                                                          with
                                                          | true ->
                                                              (match 
                                                                 (implies_intro
                                                                    ())
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (31))))))
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
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (sk_binder'
                                                                    (a3 ::
                                                                    acc) a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29)))))))
                                                               | FStar_Tactics_Result.Failed
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
                                                 (e, ps'2)))
                                 | FStar_Tactics_Result.Failed (e, ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1)))
                       | FStar_Tactics_Result.Failed (e, ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
             (fun uu___1 ->
                fun s -> FStar_Tactics_Result.Success ((acc, b), s)))
let (sk_binder :
  FStar_Reflection_Types.binder ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binders * FStar_Reflection_Types.binder)
        FStar_Tactics_Result.__result)
  = fun b -> sk_binder' [] b
let (skolem :
  unit ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.binders * FStar_Reflection_Types.binder)
        Prims.list FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (FStar_Tactics_Derived.cur_env ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (297))
                                      (Prims.of_int (11))
                                      (Prims.of_int (297))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Logic.fst"
                                (Prims.of_int (297)) (Prims.of_int (26))
                                (Prims.of_int (297)) (Prims.of_int (38))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (297)) (Prims.of_int (11))
                                  (Prims.of_int (297)) (Prims.of_int (38)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((FStar_Reflection_Builtins.binders_of_env a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (297)) (Prims.of_int (11))
                                     (Prims.of_int (297)) (Prims.of_int (38))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (298)) (Prims.of_int (2))
                            (Prims.of_int (298)) (Prims.of_int (18)))))
           with
           | true ->
               (FStar_Tactics_Util.map sk_binder a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (298)) (Prims.of_int (2))
                             (Prims.of_int (298)) (Prims.of_int (18)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')

let (easy_fill :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.repeat FStar_Tactics_Builtins.intro)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (307)) (Prims.of_int (12))
                          (Prims.of_int (307)) (Prims.of_int (24))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Logic.fst"
                            (Prims.of_int (309)) (Prims.of_int (4))
                            (Prims.of_int (310)) (Prims.of_int (10)))))
           with
           | true ->
               (match (FStar_Tactics_Derived.trytac
                         (fun uu___1 ->
                            fun ps1 ->
                              match (FStar_Tactics_Derived.apply
                                       (FStar_Reflection_Builtins.pack_ln
                                          (FStar_Reflection_Data.Tv_FVar
                                             (FStar_Reflection_Builtins.pack_fv
                                                ["FStar";
                                                "Tactics";
                                                "Logic";
                                                "lemma_from_squash"]))))
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Logic.fst"
                                                  (Prims.of_int (309))
                                                  (Prims.of_int (30))
                                                  (Prims.of_int (309))
                                                  (Prims.of_int (56))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (309))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (309))
                                                    (Prims.of_int (66)))))
                                   with
                                   | true ->
                                       (FStar_Tactics_Builtins.intro ())
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Logic.fst"
                                                     (Prims.of_int (309))
                                                     (Prims.of_int (58))
                                                     (Prims.of_int (309))
                                                     (Prims.of_int (66)))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (309))
                                          (Prims.of_int (4))
                                          (Prims.of_int (310))
                                          (Prims.of_int (10))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (309)) (Prims.of_int (12))
                                    (Prims.of_int (309)) (Prims.of_int (67))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (310)) (Prims.of_int (4))
                                      (Prims.of_int (310))
                                      (Prims.of_int (10)))))
                     with
                     | true ->
                         (FStar_Tactics_Derived.smt ())
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                                       (Prims.of_int (310))
                                       (Prims.of_int (4))
                                       (Prims.of_int (310))
                                       (Prims.of_int (10)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let easy : 'a . 'a -> 'a = fun x -> x