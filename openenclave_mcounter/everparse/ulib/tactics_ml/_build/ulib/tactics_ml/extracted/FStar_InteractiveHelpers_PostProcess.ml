open Prims
type meta_info = unit
let (focus_on_term : meta_info) =
  Obj.magic (fun uu___ -> failwith "Not yet implemented:focus_on_term")
let (end_proof :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Builtins.tadmit_t
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit))
let (unsquash_equality :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.term * FStar_Reflection_Types.term)
        FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Reflection_Formula.term_as_formula t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (31)) (Prims.of_int (14))
                          (Prims.of_int (31)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (31)) (Prims.of_int (8))
                            (Prims.of_int (33)) (Prims.of_int (13)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.Comp
                     (FStar_Reflection_Formula.Eq uu___, l, r) ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((FStar_Pervasives_Native.Some (l, r)), s))
                 | uu___ ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          (FStar_Pervasives_Native.None, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (31)) (Prims.of_int (8))
                             (Prims.of_int (33)) (Prims.of_int (13)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (pp_explore :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t FStar_InteractiveHelpers_ExploreTerm.explorer ->
          Obj.t ->
            FStar_Tactics_Types.proofstate ->
              unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ps ->
              match (FStar_Tactics_Derived.cur_goal ())
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (42)) (Prims.of_int (10))
                                  (Prims.of_int (42)) (Prims.of_int (21))))))
              with
              | FStar_Tactics_Result.Success (a1, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (43)) (Prims.of_int (2))
                                    (Prims.of_int (53)) (Prims.of_int (5)))))
                   with
                   | true ->
                       (match (FStar_Tactics_Derived.cur_env ())
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (53))
                                                  (Prims.of_int (5))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (43))
                                            (Prims.of_int (10))
                                            (Prims.of_int (43))
                                            (Prims.of_int (20))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (44))
                                              (Prims.of_int (2))
                                              (Prims.of_int (53))
                                              (Prims.of_int (5)))))
                             with
                             | true ->
                                 (match (FStar_InteractiveHelpers_Base.print_dbg
                                           dbg
                                           (Prims.strcat "[> pp_explore:\n"
                                              (FStar_Reflection_Builtins.term_to_string
                                                 a1)))
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (44))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (53))
                                                            (Prims.of_int (5))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (44))
                                                      (Prims.of_int (55))))))
                                  with
                                  | FStar_Tactics_Result.Success (a3, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (45))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (52))
                                                        (Prims.of_int (52)))))
                                       with
                                       | true ->
                                           (match (unsquash_equality a1)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (52))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (33))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a4, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (45))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (52))
                                                                  (Prims.of_int (52)))))
                                                 with
                                                 | true ->
                                                     ((match a4 with
                                                       | FStar_Pervasives_Native.Some
                                                           (l, uu___) ->
                                                           (fun ps1 ->
                                                              match (FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                                    dbg a2 l)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (36))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a5, ps'4)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "[> About to explore term:\n"
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    l)))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_ExploreTerm.explore_term
                                                                    dbg dfs
                                                                    () f x
                                                                    (FStar_InteractiveHelpers_Base.mk_genv
                                                                    a2 [] [])
                                                                    [] a5 l)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (49))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (end_proof
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (16)))))))
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
                                                                    (e, ps'5))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'4)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                       | uu___ ->
                                                           FStar_InteractiveHelpers_Base.mfail
                                                             "pp_explore: not a squashed equality"))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'3
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (45))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (52))
                                                                   (Prims.of_int (52)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3)))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
let (pp_explore_print_goal :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (61)) (Prims.of_int (4))
                             (Prims.of_int (61)) (Prims.of_int (35))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range
                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (63)) (Prims.of_int (2))
                       (Prims.of_int (63)) (Prims.of_int (28)))))
      with
      | true ->
          (pp_explore true false ()
             (Obj.magic
                (fun uu___1 ->
                   fun uu___2 ->
                     fun uu___3 ->
                       fun uu___4 ->
                         fun uu___5 ->
                           fun s ->
                             FStar_Tactics_Result.Success
                               (((), FStar_Tactics_Types.Continue), s)))
             (Obj.repr ()))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (61)) (Prims.of_int (4))
                              (Prims.of_int (61)) (Prims.of_int (35))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range
                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (63)) (Prims.of_int (2))
                        (Prims.of_int (63)) (Prims.of_int (28))))))
let (is_focus_on_term :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      Prims.bool FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (69)) (Prims.of_int (8))
                          (Prims.of_int (69)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (69)) (Prims.of_int (2))
                            (Prims.of_int (72)) (Prims.of_int (14)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          (((FStar_Reflection_Derived.flatten_name
                               (FStar_Reflection_Builtins.inspect_fv fv))
                              =
                              "FStar.InteractiveHelpers.PostProcess.focus_on_term"),
                            s))
                 | uu___ ->
                     (fun s -> FStar_Tactics_Result.Success (false, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (69)) (Prims.of_int (2))
                             (Prims.of_int (72)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (term_is_assert_or_assume :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (78)) (Prims.of_int (8))
                          (Prims.of_int (78)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (78)) (Prims.of_int (2))
                            (Prims.of_int (90)) (Prims.of_int (13)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_App
                     (hd, (a1, FStar_Reflection_Data.Q_Explicit)) ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.inspect hd)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (80))
                                            (Prims.of_int (16))
                                            (Prims.of_int (80))
                                            (Prims.of_int (26))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (80))
                                              (Prims.of_int (10))
                                              (Prims.of_int (88))
                                              (Prims.of_int (15)))))
                             with
                             | true ->
                                 ((match a2 with
                                   | FStar_Reflection_Data.Tv_FVar fv ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success
                                            ((if
                                                (((FStar_Reflection_Derived.flatten_name
                                                     (FStar_Reflection_Builtins.inspect_fv
                                                        fv))
                                                    = "Prims._assert")
                                                   ||
                                                   ((FStar_Reflection_Derived.flatten_name
                                                       (FStar_Reflection_Builtins.inspect_fv
                                                          fv))
                                                      =
                                                      "FStar.Pervasives.assert_norm"))
                                                  ||
                                                  ((FStar_Reflection_Derived.flatten_name
                                                      (FStar_Reflection_Builtins.inspect_fv
                                                         fv))
                                                     = "Prims._assume")
                                              then
                                                FStar_Pervasives_Native.Some
                                                  a1
                                              else
                                                FStar_Pervasives_Native.None),
                                              s))
                                   | uu___ ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success
                                            (FStar_Pervasives_Native.None, s))))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (80))
                                               (Prims.of_int (10))
                                               (Prims.of_int (88))
                                               (Prims.of_int (15)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          (FStar_Pervasives_Native.None, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (78)) (Prims.of_int (2))
                             (Prims.of_int (90)) (Prims.of_int (13)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (is_focused_term :
  FStar_Reflection_Data.term_view ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option
        FStar_Tactics_Result.__result)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Let (recf, attrs, uu___, def, body) ->
        (fun ps ->
           match (is_focus_on_term def)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (98)) (Prims.of_int (7))
                               (Prims.of_int (98)) (Prims.of_int (27))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (98)) (Prims.of_int (4))
                                 (Prims.of_int (98)) (Prims.of_int (52)))))
                with
                | true ->
                    (if a
                     then
                       (fun s ->
                          FStar_Tactics_Result.Success
                            ((FStar_Pervasives_Native.Some body), s))
                     else
                       (fun s ->
                          FStar_Tactics_Result.Success
                            (FStar_Pervasives_Native.None, s)))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (98)) (Prims.of_int (4))
                                  (Prims.of_int (98)) (Prims.of_int (52)))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | uu___ ->
        (fun s ->
           FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
type 'a exploration_result =
  {
  ge: FStar_InteractiveHelpers_Base.genv ;
  parents:
    (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
      Prims.list
    ;
  tgt_comp:
    FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
      FStar_Pervasives_Native.option
    ;
  res: 'a }
let __proj__Mkexploration_result__item__ge :
  'a . 'a exploration_result -> FStar_InteractiveHelpers_Base.genv =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> ge
let __proj__Mkexploration_result__item__parents :
  'a .
    'a exploration_result ->
      (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
        Prims.list
  =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> parents
let __proj__Mkexploration_result__item__tgt_comp :
  'a .
    'a exploration_result ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
        FStar_Pervasives_Native.option
  =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> tgt_comp
let __proj__Mkexploration_result__item__res :
  'a . 'a exploration_result -> 'a =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> res
let mk_exploration_result :
  'uuuuu .
    unit ->
      FStar_InteractiveHelpers_Base.genv ->
        (FStar_InteractiveHelpers_Base.genv *
          FStar_Reflection_Data.term_view) Prims.list ->
          FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
            FStar_Pervasives_Native.option ->
            'uuuuu -> 'uuuuu exploration_result
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            { ge = uu___1; parents = uu___2; tgt_comp = uu___3; res = uu___4
            }
type 'a pred_explorer =
  FStar_InteractiveHelpers_Base.genv ->
    (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
      Prims.list ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
        FStar_Pervasives_Native.option ->
        FStar_Reflection_Data.term_view ->
          FStar_Tactics_Types.proofstate ->
            'a FStar_Pervasives_Native.option FStar_Tactics_Result.__result
let find_predicated_term_explorer :
  'a .
    'a pred_explorer ->
      Prims.bool ->
        'a exploration_result FStar_Pervasives_Native.option
          FStar_InteractiveHelpers_ExploreTerm.explorer
  =
  fun pred ->
    fun dbg ->
      fun acc ->
        fun ge ->
          fun pl ->
            fun opt_c ->
              fun t ->
                fun ps ->
                  match (if FStar_Pervasives_Native.uu___is_Some acc
                         then
                           FStar_InteractiveHelpers_Base.mfail
                             "find_focused_term_explorer: non empty accumulator"
                         else (fun s -> FStar_Tactics_Result.Success ((), s)))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (117)) (Prims.of_int (2))
                                      (Prims.of_int (117))
                                      (Prims.of_int (77))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (118))
                                        (Prims.of_int (2))
                                        (Prims.of_int (124))
                                        (Prims.of_int (26)))))
                       with
                       | true ->
                           (match (if dbg
                                   then
                                     fun ps1 ->
                                       match match match (FStar_InteractiveHelpers_Base.term_view_construct
                                                            t)
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (96))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (68))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a2, ps'1) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95)))))
                                                        with
                                                        | true ->
                                                            (match match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (63))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_to_string
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (95))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                   with
                                                                   | 
                                                                   FStar_Tactics_Result.Success
                                                                    (a3,
                                                                    ps'2) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((Prims.strcat
                                                                    ":\n" a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a3, ps'2)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
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
                                                                    a2 a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'2) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'2)))
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
                                                                   "prims.fst"
                                                                   (Prims.of_int (603))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (603))
                                                                   (Prims.of_int (31)))))
                                                  with
                                                  | true ->
                                                      FStar_Tactics_Result.Success
                                                        ((Prims.strcat
                                                            "[> find_focused_term_explorer: "
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
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (120))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (120))
                                                             (Prims.of_int (96)))))
                                            with
                                            | true ->
                                                (FStar_Tactics_Builtins.print
                                                   a2)
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (120))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (120))
                                                              (Prims.of_int (96)))))))
                                       | FStar_Tactics_Result.Failed
                                           (e, ps'1) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'1)
                                   else
                                     (fun s ->
                                        FStar_Tactics_Result.Success ((), s)))
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (118))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (124))
                                                      (Prims.of_int (26))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (118))
                                                (Prims.of_int (2))
                                                (Prims.of_int (121))
                                                (Prims.of_int (7))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (124))
                                                  (Prims.of_int (26)))))
                                 with
                                 | true ->
                                     (match (pred ge pl opt_c t)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (122))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (124))
                                                                (Prims.of_int (26))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (122))
                                                          (Prims.of_int (26))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3, ps'2) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (122))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (124))
                                                            (Prims.of_int (26)))))
                                           with
                                           | true ->
                                               ((match a3 with
                                                 | FStar_Pervasives_Native.Some
                                                     ft ->
                                                     (fun s ->
                                                        FStar_Tactics_Result.Success
                                                          (((FStar_Pervasives_Native.Some
                                                               ((mk_exploration_result
                                                                   ()) ge pl
                                                                  opt_c ft)),
                                                             FStar_Tactics_Types.Abort),
                                                            s))
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     (fun s ->
                                                        FStar_Tactics_Result.Success
                                                          ((FStar_Pervasives_Native.None,
                                                             FStar_Tactics_Types.Continue),
                                                            s))))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (122))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (124))
                                                             (Prims.of_int (26)))))))
                                      | FStar_Tactics_Result.Failed (e, ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')
let find_predicated_term :
  'a .
    'a pred_explorer ->
      Prims.bool ->
        Prims.bool ->
          FStar_InteractiveHelpers_Base.genv ->
            (FStar_InteractiveHelpers_Base.genv *
              FStar_Reflection_Data.term_view) Prims.list ->
              FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
                FStar_Pervasives_Native.option ->
                FStar_Reflection_Types.term ->
                  FStar_Tactics_Types.proofstate ->
                    'a exploration_result FStar_Pervasives_Native.option
                      FStar_Tactics_Result.__result
  =
  fun pred ->
    fun dbg ->
      fun dfs ->
        fun ge ->
          fun pl ->
            fun opt_c ->
              fun t ->
                fun ps ->
                  match Obj.magic
                          ((FStar_InteractiveHelpers_ExploreTerm.explore_term
                              dbg dfs ()
                              (Obj.magic
                                 (find_predicated_term_explorer pred dbg))
                              (Obj.magic FStar_Pervasives_Native.None) ge pl
                              opt_c t)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (131))
                                         (Prims.of_int (6))
                                         (Prims.of_int (133))
                                         (Prims.of_int (39)))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (131))
                                        (Prims.of_int (2))
                                        (Prims.of_int (133))
                                        (Prims.of_int (39)))))
                       with
                       | true ->
                           FStar_Tactics_Result.Success
                             ((FStar_Pervasives_Native.fst a1),
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (131))
                                           (Prims.of_int (2))
                                           (Prims.of_int (133))
                                           (Prims.of_int (39))))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')
let (_is_focused_term_explorer : FStar_Reflection_Types.term pred_explorer) =
  fun ge -> fun pl -> fun opt_c -> fun tv -> is_focused_term tv
let (find_focused_term :
  Prims.bool ->
    Prims.bool ->
      FStar_InteractiveHelpers_Base.genv ->
        (FStar_InteractiveHelpers_Base.genv *
          FStar_Reflection_Data.term_view) Prims.list ->
          FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
            FStar_Pervasives_Native.option ->
            FStar_Reflection_Types.term ->
              FStar_Tactics_Types.proofstate ->
                FStar_Reflection_Types.term exploration_result
                  FStar_Pervasives_Native.option
                  FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun dfs ->
      fun ge ->
        fun pl ->
          fun opt_c ->
            fun t ->
              find_predicated_term _is_focused_term_explorer dbg dfs ge pl
                opt_c t
let (find_focused_term_in_current_goal :
  Prims.bool ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term exploration_result
        FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (147)) (Prims.of_int (10))
                          (Prims.of_int (147)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (148)) (Prims.of_int (2))
                            (Prims.of_int (164)) (Prims.of_int (5)))))
           with
           | true ->
               (match (FStar_Tactics_Derived.cur_env ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (148))
                                          (Prims.of_int (2))
                                          (Prims.of_int (164))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (148)) (Prims.of_int (10))
                                    (Prims.of_int (148)) (Prims.of_int (20))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (149)) (Prims.of_int (2))
                                      (Prims.of_int (164)) (Prims.of_int (5)))))
                     with
                     | true ->
                         (match (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   (Prims.strcat
                                      "[> find_focused_assert_in_current_goal:\n"
                                      (FStar_Reflection_Builtins.term_to_string
                                         a)))
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (149))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (164))
                                                    (Prims.of_int (5))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (149))
                                              (Prims.of_int (2))
                                              (Prims.of_int (149))
                                              (Prims.of_int (80))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (150))
                                                (Prims.of_int (8))
                                                (Prims.of_int (163))
                                                (Prims.of_int (75)))))
                               with
                               | true ->
                                   (match (unsquash_equality a)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (150))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (163))
                                                              (Prims.of_int (75))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (150))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (150))
                                                        (Prims.of_int (33))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'3)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'3
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (150))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (163))
                                                          (Prims.of_int (75)))))
                                         with
                                         | true ->
                                             ((match a3 with
                                               | FStar_Pervasives_Native.Some
                                                   (l, uu___) ->
                                                   (fun ps1 ->
                                                      match (FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                               dbg a1 l)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (36))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4, ps'4) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (7)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (7))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (7)))))
                                                                with
                                                                | true ->
                                                                    (
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "[> About to explore term:\n"
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    l)))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (7))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (7))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (154))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (32)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (find_focused_term
                                                                    dbg true
                                                                    (FStar_InteractiveHelpers_Base.mk_genv
                                                                    a1 [] [])
                                                                    [] a4 l)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (32))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (52))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (32)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a6
                                                                    with
                                                                    | FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "[> Found focused term:\n"
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    res.res)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (73))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (14)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (res,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (14))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7))
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    (Prims.strcat
                                                                    "find_focused_term_in_current_goal: could not find a focused term in the current goal: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (32)))))))
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
                                                                    (e, ps'5))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4))
                                               | uu___ ->
                                                   FStar_InteractiveHelpers_Base.mfail
                                                     "find_focused_term_in_current_goal: not a squashed equality"))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'3
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (150))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (163))
                                                           (Prims.of_int (75)))))))
                                    | FStar_Tactics_Result.Failed (e, ps'3)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'3)))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (find_focused_assert_in_current_goal :
  Prims.bool ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term exploration_result
        FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ps ->
      match (FStar_InteractiveHelpers_Base.print_dbg dbg
               "[> find_focused_assert_in_current_goal")
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (169)) (Prims.of_int (2))
                          (Prims.of_int (169)) (Prims.of_int (58))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (170)) (Prims.of_int (2))
                            (Prims.of_int (183)) (Prims.of_int (5)))))
           with
           | true ->
               (match (find_focused_term_in_current_goal dbg)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (170))
                                          (Prims.of_int (2))
                                          (Prims.of_int (183))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (170)) (Prims.of_int (12))
                                    (Prims.of_int (170)) (Prims.of_int (49))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (171)) (Prims.of_int (2))
                                      (Prims.of_int (183)) (Prims.of_int (5)))))
                     with
                     | true ->
                         (match (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   (Prims.strcat "[> Found focused term:\n"
                                      (FStar_Reflection_Builtins.term_to_string
                                         a1.res)))
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (171))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (183))
                                                    (Prims.of_int (5))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (171))
                                              (Prims.of_int (2))
                                              (Prims.of_int (171))
                                              (Prims.of_int (69))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (173))
                                                (Prims.of_int (2))
                                                (Prims.of_int (183))
                                                (Prims.of_int (5)))))
                               with
                               | true ->
                                   (match match (FStar_Tactics_Builtins.inspect
                                                   a1.res)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (5))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (14))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (174))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (174))
                                                              (Prims.of_int (25))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a3, ps'3) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'3
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (174))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (178))
                                                                (Prims.of_int (14)))))
                                               with
                                               | true ->
                                                   ((match a3 with
                                                     | FStar_Reflection_Data.Tv_Let
                                                         (uu___, uu___1, bv0,
                                                          fterm, uu___2)
                                                         ->
                                                         (fun ps1 ->
                                                            match (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    a1.ge bv0
                                                                    false
                                                                    FStar_Pervasives_Native.None)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (50))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a4, ps'4) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (42)))))
                                                                 with
                                                                 | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ({
                                                                    ge = a4;
                                                                    parents =
                                                                    (a1.parents);
                                                                    tgt_comp
                                                                    =
                                                                    (a1.tgt_comp);
                                                                    res =
                                                                    fterm
                                                                    },
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (42))))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps'4) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'4))
                                                     | uu___ ->
                                                         (fun s ->
                                                            FStar_Tactics_Result.Success
                                                              (a1, s))))
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'3
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (174))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (178))
                                                                 (Prims.of_int (14)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'3) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'3)
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'3)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'3
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (180))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (182))
                                                          (Prims.of_int (38)))))
                                         with
                                         | true ->
                                             (match (term_is_assert_or_assume
                                                       a3.res)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (38))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (180))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (180))
                                                                  (Prims.of_int (47))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a4, ps'4) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'4
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (38)))))
                                                   with
                                                   | true ->
                                                       ((match a4 with
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             FStar_InteractiveHelpers_Base.mfail
                                                               (Prims.strcat
                                                                  "find_focused_assert_in_current_goal: the found focused term is not an assertion or an assumption:"
                                                                  (FStar_Reflection_Builtins.term_to_string
                                                                    a1.res))
                                                         | FStar_Pervasives_Native.Some
                                                             tm ->
                                                             (fun s ->
                                                                FStar_Tactics_Result.Success
                                                                  ({
                                                                    ge =
                                                                    (a3.ge);
                                                                    parents =
                                                                    (a3.parents);
                                                                    tgt_comp
                                                                    =
                                                                    (a3.tgt_comp);
                                                                    res = tm
                                                                   }, s))))
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'4
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (38)))))))
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
let (analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStar_Reflection_Types.term exploration_result ->
          FStar_Tactics_Types.proofstate ->
            unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun res ->
          fun ps ->
            match FStar_Tactics_Types.tracepoint
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (199)) (Prims.of_int (11))
                                   (Prims.of_int (199)) (Prims.of_int (17))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (200)) (Prims.of_int (2))
                             (Prims.of_int (256)) (Prims.of_int (30)))))
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
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (199))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (199))
                                                    (Prims.of_int (17))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (200))
                                              (Prims.of_int (2))
                                              (Prims.of_int (256))
                                              (Prims.of_int (30))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (200))
                                        (Prims.of_int (14))
                                        (Prims.of_int (200))
                                        (Prims.of_int (26))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (202)) (Prims.of_int (2))
                                  (Prims.of_int (256)) (Prims.of_int (30)))))
                 with
                 | true ->
                     (match match (FStar_Tactics_Builtins.inspect res.res)
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
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (17))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (200))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (200))
                                                                  (Prims.of_int (26))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (202))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (256))
                                                            (Prims.of_int (30))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (203))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (230))
                                                      (Prims.of_int (82))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (203))
                                                (Prims.of_int (16))
                                                (Prims.of_int (203))
                                                (Prims.of_int (31))))))
                            with
                            | FStar_Tactics_Result.Success (a, ps') ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (203))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (230))
                                                  (Prims.of_int (82)))))
                                 with
                                 | true ->
                                     ((match a with
                                       | FStar_Reflection_Data.Tv_Let
                                           (uu___, uu___1, bv0, fterm,
                                            uu___2)
                                           ->
                                           (fun ps1 ->
                                              match (FStar_InteractiveHelpers_Base.print_dbg
                                                       dbg
                                                       (Prims.strcat
                                                          "Restraining to: "
                                                          (FStar_Reflection_Builtins.term_to_string
                                                             fterm)))
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (210))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (210))
                                                                  (Prims.of_int (63))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a1, ps'1) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (35))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    res.ge
                                                                    bv0 false
                                                                    FStar_Pervasives_Native.None)
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (46))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a2, ps'2)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
                                                                  with
                                                                  | true ->
                                                                    (match 
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Variable bound in let: "
                                                                    (FStar_InteractiveHelpers_Base.abv_to_string
                                                                    bv0)))
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
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (77))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv0).FStar_Reflection_Data.bv_ppname
                                                                    = "uu___"
                                                                    then
                                                                    FStar_InteractiveHelpers_Base.genv_push_fresh_bv
                                                                    a2 "ret"
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv0).FStar_Reflection_Data.bv_sort
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    bv0), s)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (21)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | (ge2,
                                                                    bv1) ->
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                                    dbg
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    fterm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (228))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge2,
                                                                    fterm,
                                                                    a4,
                                                                    (FStar_Pervasives_Native.Some
                                                                    bv1),
                                                                    ((match 
                                                                    FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    res.ge
                                                                    (FStar_Reflection_Derived.name_of_bv
                                                                    bv0)
                                                                    with
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | FStar_Pervasives_Native.Some
                                                                    (sbv,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    sbv)),
                                                                    true),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (69)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'2) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'2))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'1) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'1))
                                       | uu___ ->
                                           (fun ps1 ->
                                              match (FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                       dbg
                                                       (res.ge).FStar_InteractiveHelpers_Base.env
                                                       res.res)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (25))
                                                                  (Prims.of_int (230))
                                                                  (Prims.of_int (62))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a1, ps'1) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (82)))))
                                                   with
                                                   | true ->
                                                       FStar_Tactics_Result.Success
                                                         (((res.ge),
                                                            (res.res), a1,
                                                            FStar_Pervasives_Native.None,
                                                            FStar_Pervasives_Native.None,
                                                            false),
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'1
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (82))))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'1) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'1))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (203))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (230))
                                                   (Prims.of_int (82)))))))
                            | FStar_Tactics_Result.Failed (e, ps') ->
                                FStar_Tactics_Result.Failed (e, ps')
                      with
                      | FStar_Tactics_Result.Success (a, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (202))
                                            (Prims.of_int (2))
                                            (Prims.of_int (256))
                                            (Prims.of_int (30)))))
                           with
                           | true ->
                               ((match a with
                                 | (ge1, studied_term, info, ret_bv,
                                    shadowed_bv, is_let) ->
                                     (fun ps1 ->
                                        match match match (FStar_InteractiveHelpers_Base.term_construct
                                                             studied_term)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (79))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (79))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (78))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a1, ps'1) ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
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
                                                                   "[> Focused term constructor: "
                                                                   a1),
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
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
                                                  (a1, ps'1) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (79)))))
                                                   with
                                                   | true ->
                                                       (FStar_InteractiveHelpers_Base.print_dbg
                                                          dbg a1)
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (79)))))))
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
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (234))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (256))
                                                              (Prims.of_int (30)))))
                                             with
                                             | true ->
                                                 (match (FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           (Prims.strcat
                                                              "[> Environment information (after effect analysis):\n"
                                                              (FStar_InteractiveHelpers_Base.genv_to_string
                                                                 ge1)))
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (94))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a2, ps'2) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                       with
                                                       | true ->
                                                           (match match 
                                                                    (term_is_assert_or_assume
                                                                    studied_term)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (63))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (63)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.uu___is_Some
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (63))))))))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a3, ps'3) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                 with
                                                                 | true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.opt_tapply
                                                                    (fun x ->
                                                                    FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    x))
                                                                    ret_bv)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (60))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
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
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Effectful.eterm_info_to_assertions
                                                                    dbg
                                                                    with_gpre
                                                                    with_gpost
                                                                    ge1
                                                                    studied_term
                                                                    is_let a3
                                                                    info a4
                                                                    res.tgt_comp
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    res.parents)
                                                                    [])
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (245))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | (ge2,
                                                                    asserts)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Propositions.simp_filter_assertions
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                                                                    asserts)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (71))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    shadowed_bv
                                                                    a6)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (86))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a7
                                                                    with
                                                                    | (ge3,
                                                                    asserts1)
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    (if
                                                                    is_let
                                                                    then
                                                                    asserts1
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    (FStar_List_Tot_Base.append
                                                                    asserts1.FStar_InteractiveHelpers_Propositions.pres
                                                                    asserts1.FStar_InteractiveHelpers_Propositions.posts)
                                                                    []))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (30)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
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
                                                        (e, ps'2)))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps'1) ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps'1))))
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (202))
                                             (Prims.of_int (2))
                                             (Prims.of_int (256))
                                             (Prims.of_int (30)))))))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')))
let (pp_analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        unit ->
          FStar_Tactics_Types.proofstate ->
            unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun uu___ ->
          FStar_Tactics_Derived.try_with
            (fun uu___1 ->
               match () with
               | () ->
                   (fun ps ->
                      match (find_focused_term_in_current_goal dbg)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (262))
                                          (Prims.of_int (14))
                                          (Prims.of_int (262))
                                          (Prims.of_int (51))))))
                      with
                      | FStar_Tactics_Result.Success (a, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (263))
                                            (Prims.of_int (4))
                                            (Prims.of_int (264))
                                            (Prims.of_int (16)))))
                           with
                           | true ->
                               (match (analyze_effectful_term dbg with_gpre
                                         with_gpost a)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (263))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (264))
                                                          (Prims.of_int (16))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (263))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (263))
                                                    (Prims.of_int (55))))))
                                with
                                | FStar_Tactics_Result.Success (a1, ps'1) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (264))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (264))
                                                      (Prims.of_int (16)))))
                                     with
                                     | true ->
                                         (end_proof ())
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (264))
                                                       (Prims.of_int (16)))))))
                                | FStar_Tactics_Result.Failed (e, ps'1) ->
                                    FStar_Tactics_Result.Failed (e, ps'1)))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')))
            (fun uu___1 ->
               match uu___1 with
               | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                   (fun ps ->
                      match (FStar_InteractiveHelpers_Output.printout_failure
                               msg)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (265))
                                          (Prims.of_int (29))
                                          (Prims.of_int (265))
                                          (Prims.of_int (49))))))
                      with
                      | FStar_Tactics_Result.Success (a, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (265))
                                            (Prims.of_int (51))
                                            (Prims.of_int (265))
                                            (Prims.of_int (63)))))
                           with
                           | true ->
                               (end_proof ())
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (265))
                                             (Prims.of_int (51))
                                             (Prims.of_int (265))
                                             (Prims.of_int (63)))))))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps'))
               | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_analyze_effectful_term"
    (Prims.of_int (5))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_4
             (FStar_Tactics_Native.from_tactic_4 pp_analyze_effectful_term)
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_bool
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_unit
             FStar_Syntax_Embeddings.e_unit psc ncb args)
let (remove_b2t :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (281)) (Prims.of_int (8))
                          (Prims.of_int (281)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (281)) (Prims.of_int (2))
                            (Prims.of_int (288)) (Prims.of_int (10)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_App
                     (hd, (a1, FStar_Reflection_Data.Q_Explicit)) ->
                     (fun ps1 ->
                        match (FStar_Tactics_Builtins.inspect hd)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (283))
                                            (Prims.of_int (16))
                                            (Prims.of_int (283))
                                            (Prims.of_int (26))))))
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (283))
                                              (Prims.of_int (10))
                                              (Prims.of_int (286))
                                              (Prims.of_int (12)))))
                             with
                             | true ->
                                 ((match a2 with
                                   | FStar_Reflection_Data.Tv_FVar fv ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success
                                            ((if
                                                FStar_InteractiveHelpers_Base.fv_eq_name
                                                  fv
                                                  FStar_Reflection_Const.b2t_qn
                                              then a1
                                              else t), s))
                                   | uu___ ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success (t, s))))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (283))
                                               (Prims.of_int (10))
                                               (Prims.of_int (286))
                                               (Prims.of_int (12)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___ -> (fun s -> FStar_Tactics_Result.Success (t, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (281)) (Prims.of_int (2))
                             (Prims.of_int (288)) (Prims.of_int (10)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (is_conjunction :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.term * FStar_Reflection_Types.term)
        FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (remove_b2t t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (294)) (Prims.of_int (10))
                          (Prims.of_int (294)) (Prims.of_int (22))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (295)) (Prims.of_int (2))
                            (Prims.of_int (305)) (Prims.of_int (13)))))
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
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (295))
                                             (Prims.of_int (2))
                                             (Prims.of_int (305))
                                             (Prims.of_int (13))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (295))
                                       (Prims.of_int (19))
                                       (Prims.of_int (295))
                                       (Prims.of_int (32))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (295)) (Prims.of_int (2))
                                 (Prims.of_int (305)) (Prims.of_int (13)))))
                with
                | true ->
                    ((match FStar_Reflection_Derived.collect_app a with
                      | (hd, params) ->
                          (match params with
                           | (x, FStar_Reflection_Data.Q_Explicit)::(y,
                                                                    FStar_Reflection_Data.Q_Explicit)::[]
                               ->
                               (fun ps1 ->
                                  match (FStar_Tactics_Builtins.inspect hd)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (298))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (298))
                                                      (Prims.of_int (26))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (298))
                                                        (Prims.of_int (10))
                                                        (Prims.of_int (303))
                                                        (Prims.of_int (15)))))
                                       with
                                       | true ->
                                           ((match a1 with
                                             | FStar_Reflection_Data.Tv_FVar
                                                 fv ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      ((if
                                                          ((FStar_Reflection_Builtins.inspect_fv
                                                              fv)
                                                             =
                                                             FStar_Reflection_Const.and_qn)
                                                            ||
                                                            ((FStar_Reflection_Builtins.inspect_fv
                                                                fv)
                                                               =
                                                               ["Prims";
                                                               "op_AmpAmp"])
                                                        then
                                                          FStar_Pervasives_Native.Some
                                                            (x, y)
                                                        else
                                                          FStar_Pervasives_Native.None),
                                                        s))
                                             | uu___ ->
                                                 (fun s ->
                                                    FStar_Tactics_Result.Success
                                                      (FStar_Pervasives_Native.None,
                                                        s))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (298))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (303))
                                                         (Prims.of_int (15)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1))
                           | uu___ ->
                               (fun s ->
                                  FStar_Tactics_Result.Success
                                    (FStar_Pervasives_Native.None, s)))))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (295))
                                              (Prims.of_int (2))
                                              (Prims.of_int (305))
                                              (Prims.of_int (13))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (295))
                                        (Prims.of_int (19))
                                        (Prims.of_int (295))
                                        (Prims.of_int (32))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (295)) (Prims.of_int (2))
                                  (Prims.of_int (305)) (Prims.of_int (13))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (_split_conjunctions :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term Prims.list FStar_Tactics_Result.__result)
  =
  fun ls ->
    fun t ->
      fun ps ->
        match (is_conjunction t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (310)) (Prims.of_int (8))
                            (Prims.of_int (310)) (Prims.of_int (24))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (310)) (Prims.of_int (2))
                              (Prims.of_int (315)) (Prims.of_int (7)))))
             with
             | true ->
                 ((match a with
                   | FStar_Pervasives_Native.None ->
                       (fun s -> FStar_Tactics_Result.Success ((t :: ls), s))
                   | FStar_Pervasives_Native.Some (l, r) ->
                       (fun ps1 ->
                          match (_split_conjunctions ls r)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (313))
                                              (Prims.of_int (14))
                                              (Prims.of_int (313))
                                              (Prims.of_int (38))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (314))
                                                (Prims.of_int (4))
                                                (Prims.of_int (315))
                                                (Prims.of_int (7)))))
                               with
                               | true ->
                                   (match (_split_conjunctions a1 l)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (314))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (315))
                                                              (Prims.of_int (7))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (314))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (314))
                                                        (Prims.of_int (39))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'2)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'2
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (314))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (314))
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
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (314))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (314))
                                                             (Prims.of_int (11))))))))
                                    | FStar_Tactics_Result.Failed (e, ps'2)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'2)))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (310)) (Prims.of_int (2))
                               (Prims.of_int (315)) (Prims.of_int (7)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (split_conjunctions :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term Prims.list FStar_Tactics_Result.__result)
  = fun t -> _split_conjunctions [] t
let (split_conjunctions_under_match :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term Prims.list FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun t ->
      fun ps ->
        match (remove_b2t t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (329)) (Prims.of_int (11))
                            (Prims.of_int (329)) (Prims.of_int (23))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (330)) (Prims.of_int (2))
                              (Prims.of_int (337)) (Prims.of_int (7)))))
             with
             | true ->
                 (match match match (FStar_InteractiveHelpers_Base.term_construct
                                       a)
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (7))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (330))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (330))
                                                              (Prims.of_int (75))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (330))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (330))
                                                        (Prims.of_int (75))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (330))
                                                  (Prims.of_int (57))
                                                  (Prims.of_int (330))
                                                  (Prims.of_int (74))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
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
                                             "[> split_conjunctions_under_match: "
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
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (330))
                                              (Prims.of_int (2))
                                              (Prims.of_int (330))
                                              (Prims.of_int (75)))))
                             with
                             | true ->
                                 (FStar_InteractiveHelpers_Base.print_dbg dbg
                                    a1)
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (330))
                                               (Prims.of_int (2))
                                               (Prims.of_int (330))
                                               (Prims.of_int (75)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)
                  with
                  | FStar_Tactics_Result.Success (a1, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (331))
                                        (Prims.of_int (2))
                                        (Prims.of_int (337))
                                        (Prims.of_int (7)))))
                       with
                       | true ->
                           (match (FStar_Tactics_Builtins.inspect a)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (331))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (337))
                                                      (Prims.of_int (7))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (331))
                                                (Prims.of_int (8))
                                                (Prims.of_int (331))
                                                (Prims.of_int (18))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'2) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'2
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (331))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (337))
                                                  (Prims.of_int (7)))))
                                 with
                                 | true ->
                                     ((match a2 with
                                       | FStar_Reflection_Data.Tv_Match
                                           (scrut, ret_opt, (pat, br)::[]) ->
                                           (fun ps1 ->
                                              match (split_conjunctions br)
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (333))
                                                                  (Prims.of_int (13))
                                                                  (Prims.of_int (333))
                                                                  (Prims.of_int (34))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a3, ps'3) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'3
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (62)))))
                                                   with
                                                   | true ->
                                                       (FStar_Tactics_Util.map
                                                          (fun x ->
                                                             FStar_Tactics_Builtins.pack
                                                               (FStar_Reflection_Data.Tv_Match
                                                                  (scrut,
                                                                    ret_opt,
                                                                    [
                                                                    (pat, x)])))
                                                          a3)
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'3
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (62)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'3) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'3))
                                       | uu___ ->
                                           (fun s ->
                                              FStar_Tactics_Result.Success
                                                ([t], s))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (331))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (337))
                                                   (Prims.of_int (7)))))))
                            | FStar_Tactics_Result.Failed (e, ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (split_assert_conjs :
  Prims.bool ->
    FStar_Reflection_Types.term exploration_result ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun res ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (341)) (Prims.of_int (12))
                               (Prims.of_int (341)) (Prims.of_int (18))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range
                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (343)) (Prims.of_int (2))
                         (Prims.of_int (356)) (Prims.of_int (30)))))
        with
        | true ->
            (match (FStar_Tactics_Builtins.norm_term_env
                      (res.ge).FStar_InteractiveHelpers_Base.env
                      FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                      res.res)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (341))
                                             (Prims.of_int (12))
                                             (Prims.of_int (341))
                                             (Prims.of_int (18))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (343))
                                       (Prims.of_int (2))
                                       (Prims.of_int (356))
                                       (Prims.of_int (30))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (343)) (Prims.of_int (10))
                                 (Prims.of_int (343)) (Prims.of_int (56))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (345)) (Prims.of_int (2))
                                   (Prims.of_int (356)) (Prims.of_int (30)))))
                  with
                  | true ->
                      (match (split_conjunctions a)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (345))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (356))
                                                 (Prims.of_int (30))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (345))
                                           (Prims.of_int (14))
                                           (Prims.of_int (345))
                                           (Prims.of_int (34))))))
                       with
                       | FStar_Tactics_Result.Success (a1, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (350))
                                             (Prims.of_int (2))
                                             (Prims.of_int (356))
                                             (Prims.of_int (30)))))
                            with
                            | true ->
                                (match (if
                                          (FStar_List_Tot_Base.length a1) =
                                            Prims.int_one
                                        then
                                          split_conjunctions_under_match dbg
                                            a
                                        else
                                          (fun s ->
                                             FStar_Tactics_Result.Success
                                               (a1, s)))
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (350))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (356))
                                                           (Prims.of_int (30))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (351))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (352))
                                                     (Prims.of_int (14))))))
                                 with
                                 | FStar_Tactics_Result.Success (a2, ps'2) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'2
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (354))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (356))
                                                       (Prims.of_int (30)))))
                                      with
                                      | true ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (30))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (38))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (356))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (356))
                                                            (Prims.of_int (30)))))
                                           with
                                           | true ->
                                               (FStar_InteractiveHelpers_Output.printout_success
                                                  res.ge
                                                  (FStar_InteractiveHelpers_Propositions.mk_assertions
                                                     a2 []))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (30))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (354))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (354))
                                                                   (Prims.of_int (38))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (356))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (356))
                                                             (Prims.of_int (30))))))))
                                 | FStar_Tactics_Result.Failed (e, ps'2) ->
                                     FStar_Tactics_Result.Failed (e, ps'2)))
                       | FStar_Tactics_Result.Failed (e, ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (pp_split_assert_conjs :
  Prims.bool ->
    unit ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               (fun ps ->
                  match (find_focused_assert_in_current_goal dbg)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (362))
                                      (Prims.of_int (14))
                                      (Prims.of_int (362))
                                      (Prims.of_int (53))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (363))
                                        (Prims.of_int (4))
                                        (Prims.of_int (364))
                                        (Prims.of_int (16)))))
                       with
                       | true ->
                           (match (split_assert_conjs dbg a)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (363))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (364))
                                                      (Prims.of_int (16))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (363))
                                                (Prims.of_int (4))
                                                (Prims.of_int (363))
                                                (Prims.of_int (30))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (364))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (364))
                                                  (Prims.of_int (16)))))
                                 with
                                 | true ->
                                     (end_proof ())
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (16)))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
        (fun uu___1 ->
           match uu___1 with
           | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
               (fun ps ->
                  match (FStar_InteractiveHelpers_Output.printout_failure msg)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (365))
                                      (Prims.of_int (29))
                                      (Prims.of_int (365))
                                      (Prims.of_int (49))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (365))
                                        (Prims.of_int (51))
                                        (Prims.of_int (365))
                                        (Prims.of_int (63)))))
                       with
                       | true ->
                           (end_proof ())
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (365))
                                         (Prims.of_int (51))
                                         (Prims.of_int (365))
                                         (Prims.of_int (63)))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps'))
           | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_split_assert_conjs"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2 pp_split_assert_conjs)
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_unit
             FStar_Syntax_Embeddings.e_unit psc ncb args)
type eq_kind =
  | Eq_Dec of FStar_Reflection_Types.typ 
  | Eq_Undec of FStar_Reflection_Types.typ 
  | Eq_Hetero of FStar_Reflection_Types.typ * FStar_Reflection_Types.typ 
let (uu___is_Eq_Dec : eq_kind -> Prims.bool) =
  fun projectee -> match projectee with | Eq_Dec _0 -> true | uu___ -> false
let (__proj__Eq_Dec__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Dec _0 -> _0
let (uu___is_Eq_Undec : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Undec _0 -> true | uu___ -> false
let (__proj__Eq_Undec__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Undec _0 -> _0
let (uu___is_Eq_Hetero : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Hetero (_0, _1) -> true | uu___ -> false
let (__proj__Eq_Hetero__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _0
let (__proj__Eq_Hetero__item___1 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _1
let (is_eq :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        (eq_kind * FStar_Reflection_Types.term * FStar_Reflection_Types.term)
          FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun t ->
      fun ps ->
        match (remove_b2t t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (386)) (Prims.of_int (10))
                            (Prims.of_int (386)) (Prims.of_int (22))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (387)) (Prims.of_int (2))
                              (Prims.of_int (407)) (Prims.of_int (13)))))
             with
             | true ->
                 (match (FStar_InteractiveHelpers_Base.print_dbg dbg
                           (Prims.strcat "[> is_eq: "
                              (FStar_Reflection_Builtins.term_to_string a)))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (387))
                                            (Prims.of_int (2))
                                            (Prims.of_int (407))
                                            (Prims.of_int (13))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (387)) (Prims.of_int (2))
                                      (Prims.of_int (387))
                                      (Prims.of_int (49))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (388))
                                        (Prims.of_int (2))
                                        (Prims.of_int (407))
                                        (Prims.of_int (13)))))
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
                                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (388))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (407))
                                                         (Prims.of_int (13))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (388))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (388))
                                                   (Prims.of_int (32))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (388))
                                             (Prims.of_int (2))
                                             (Prims.of_int (407))
                                             (Prims.of_int (13)))))
                            with
                            | true ->
                                ((match FStar_Reflection_Derived.collect_app
                                          a
                                  with
                                  | (hd, params) ->
                                      (fun ps1 ->
                                         match (FStar_InteractiveHelpers_Base.print_dbg
                                                  dbg
                                                  (Prims.strcat "- hd:\n"
                                                     (FStar_Reflection_Builtins.term_to_string
                                                        hd)))
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (389))
                                                             (Prims.of_int (47))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a2, ps'2) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (390))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (407))
                                                               (Prims.of_int (13)))))
                                              with
                                              | true ->
                                                  (match (FStar_InteractiveHelpers_Base.print_dbg
                                                            dbg
                                                            (Prims.strcat
                                                               "- parameters:\n"
                                                               (FStar_InteractiveHelpers_Base.list_to_string
                                                                  (fun uu___
                                                                    ->
                                                                    match uu___
                                                                    with
                                                                    | 
                                                                    (x, y) ->
                                                                    FStar_Reflection_Builtins.term_to_string
                                                                    x) params)))
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (13))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (92))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a3, ps'3) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'3
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (13)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_Tactics_Builtins.inspect
                                                                    hd)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (18))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (13)))))
                                                                  with
                                                                  | true ->
                                                                    ((match a4
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((match params
                                                                    with
                                                                    | (a5,
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStar_Reflection_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStar_Reflection_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    (((FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.op_Equality")
                                                                    ||
                                                                    ((FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.equals"))
                                                                    ||
                                                                    ((FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.op_Equals")
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Dec
                                                                    a5), x,
                                                                    y)
                                                                    else
                                                                    if
                                                                    ((FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.eq2")
                                                                    ||
                                                                    ((FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.op_Equals_Equals")
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Undec
                                                                    a5), x,
                                                                    y)
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | (a5,
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (b,
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStar_Reflection_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStar_Reflection_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)) =
                                                                    "Prims.op_Equals_Equals_Equals"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Hetero
                                                                    (a5, b)),
                                                                    x, y)
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | uu___
                                                                    ->
                                                                    FStar_Pervasives_Native.None),
                                                                    s))
                                                                    | uu___
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    s))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (13)))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'4) ->
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
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (388))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (407))
                                                          (Prims.of_int (13))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (388))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (388))
                                                    (Prims.of_int (32))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (388))
                                              (Prims.of_int (2))
                                              (Prims.of_int (407))
                                              (Prims.of_int (13))))))))
                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (mk_eq :
  eq_kind ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        match k with
        | Eq_Dec ty ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["Prims"; "op_Equality"])))
              [(ty, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
        | Eq_Undec ty ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv ["Prims"; "eq2"])))
              [(ty, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
        | Eq_Hetero (ty1, ty2) ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["Prims"; "op_Equals_Equals_Equals"])))
              [(ty1, FStar_Reflection_Data.Q_Implicit);
              (ty2, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
let (formula_construct :
  FStar_Reflection_Formula.formula ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun f ->
    fun s ->
      FStar_Tactics_Result.Success
        ((match f with
          | FStar_Reflection_Formula.True_ -> "True_"
          | FStar_Reflection_Formula.False_ -> "False_"
          | FStar_Reflection_Formula.Comp (uu___, uu___1, uu___2) -> "Comp"
          | FStar_Reflection_Formula.And (uu___, uu___1) -> "And"
          | FStar_Reflection_Formula.Or (uu___, uu___1) -> "Or"
          | FStar_Reflection_Formula.Not uu___ -> "Not"
          | FStar_Reflection_Formula.Implies (uu___, uu___1) -> "Implies"
          | FStar_Reflection_Formula.Iff (uu___, uu___1) -> "Iff"
          | FStar_Reflection_Formula.Forall (uu___, uu___1) -> "Forall"
          | FStar_Reflection_Formula.Exists (uu___, uu___1) -> "Exists"
          | FStar_Reflection_Formula.App (uu___, uu___1) -> "Apply"
          | FStar_Reflection_Formula.Name uu___ -> "Name"
          | FStar_Reflection_Formula.FV uu___ -> "FV"
          | FStar_Reflection_Formula.IntLit uu___ -> "IntLit"
          | FStar_Reflection_Formula.F_Unknown -> "F_Unknown"), s)
let (is_equality_for_term :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        fun ps ->
          match (FStar_InteractiveHelpers_Base.print_dbg dbg
                   (Prims.strcat "[> is_equality_for_term:"
                      (Prims.strcat "\n- term: "
                         (Prims.strcat
                            (FStar_Reflection_Builtins.term_to_string tm)
                            (Prims.strcat "\n- prop: "
                               (FStar_Reflection_Builtins.term_to_string p))))))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (443)) (Prims.of_int (2))
                              (Prims.of_int (445)) (Prims.of_int (49))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (448)) (Prims.of_int (2))
                                (Prims.of_int (469)) (Prims.of_int (8)))))
               with
               | true ->
                   (match match (FStar_Tactics_Builtins.inspect tm)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (448))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (469))
                                                          (Prims.of_int (8))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (449))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (452))
                                                    (Prims.of_int (38))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (449))
                                              (Prims.of_int (10))
                                              (Prims.of_int (449))
                                              (Prims.of_int (20))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (449))
                                                (Prims.of_int (4))
                                                (Prims.of_int (452))
                                                (Prims.of_int (38)))))
                               with
                               | true ->
                                   ((match a1 with
                                     | FStar_Reflection_Data.Tv_Var bv ->
                                         (fun s ->
                                            FStar_Tactics_Result.Success
                                              ((fun tm' ->
                                                  fun ps1 ->
                                                    match (FStar_Tactics_Builtins.inspect
                                                             tm')
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (35))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a2, ps'2) ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (35)))))
                                                         with
                                                         | true ->
                                                             ((match a2 with
                                                               | FStar_Reflection_Data.Tv_Var
                                                                   bv' ->
                                                                   (fun s1 ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_InteractiveHelpers_Base.bv_eq
                                                                    bv bv'),
                                                                    s1))
                                                               | uu___ ->
                                                                   (fun s1 ->
                                                                    FStar_Tactics_Result.Success
                                                                    (false,
                                                                    s1))))
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (35)))))))
                                                    | FStar_Tactics_Result.Failed
                                                        (e, ps'2) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps'2)), s))
                                     | uu___ ->
                                         (fun s ->
                                            FStar_Tactics_Result.Success
                                              ((fun tm' ->
                                                  fun s1 ->
                                                    FStar_Tactics_Result.Success
                                                      ((FStar_Reflection_Builtins.term_eq
                                                          tm tm'), s1)), s))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (449))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (452))
                                                 (Prims.of_int (38)))))))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)
                    with
                    | FStar_Tactics_Result.Success (a1, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (454))
                                          (Prims.of_int (2))
                                          (Prims.of_int (469))
                                          (Prims.of_int (8)))))
                         with
                         | true ->
                             (match (is_eq dbg p)
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (454))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (469))
                                                        (Prims.of_int (8))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (454))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (454))
                                                  (Prims.of_int (19))))))
                              with
                              | FStar_Tactics_Result.Success (a2, ps'2) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'2
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (454))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (469))
                                                    (Prims.of_int (8)))))
                                   with
                                   | true ->
                                       ((match a2 with
                                         | FStar_Pervasives_Native.Some
                                             (ekind, l, r) ->
                                             (fun ps1 ->
                                                match (FStar_InteractiveHelpers_Base.print_dbg
                                                         dbg
                                                         (Prims.strcat
                                                            "Term is eq: "
                                                            (Prims.strcat
                                                               (FStar_Reflection_Builtins.term_to_string
                                                                  l)
                                                               (Prims.strcat
                                                                  " = "
                                                                  (FStar_Reflection_Builtins.term_to_string
                                                                    r)))))
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (80))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a3, ps'3) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'3
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))
                                                     with
                                                     | true ->
                                                         (if
                                                            uu___is_Eq_Hetero
                                                              ekind
                                                          then
                                                            (fun ps2 ->
                                                               match 
                                                                 (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Ignoring heterogeneous equality")
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (461))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (461))
                                                                    (Prims.of_int (53))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (10)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (10))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e, ps'4)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                          else
                                                            (fun ps2 ->
                                                               match 
                                                                 (a1 l)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (22))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a4
                                                                    then
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    r), s))
                                                                    else
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (a1 r)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (22))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a5
                                                                    then
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    l), s))
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    s)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e, ps'4)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'3
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (13)))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e, ps'3) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'3))
                                         | uu___ ->
                                             (fun ps1 ->
                                                match (FStar_InteractiveHelpers_Base.print_dbg
                                                         dbg "Term is not eq")
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (34))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a3, ps'3) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'3
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (8)))))
                                                     with
                                                     | true ->
                                                         FStar_Tactics_Result.Success
                                                           (FStar_Pervasives_Native.None,
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'3
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (8))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e, ps'3) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'3))))
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (454))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (469))
                                                     (Prims.of_int (8)))))))
                              | FStar_Tactics_Result.Failed (e, ps'2) ->
                                  FStar_Tactics_Result.Failed (e, ps'2)))
                    | FStar_Tactics_Result.Failed (e, ps'1) ->
                        FStar_Tactics_Result.Failed (e, ps'1)))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (find_subequality :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          FStar_Reflection_Types.term FStar_Pervasives_Native.option
            FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        fun ps ->
          match (FStar_InteractiveHelpers_Base.print_dbg dbg
                   (Prims.strcat "[> find_subequality:"
                      (Prims.strcat "\n- ter  : "
                         (Prims.strcat
                            (FStar_Reflection_Builtins.term_to_string tm)
                            (Prims.strcat "\n- props: "
                               (FStar_Reflection_Builtins.term_to_string p))))))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (473)) (Prims.of_int (2))
                              (Prims.of_int (475)) (Prims.of_int (50))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (476)) (Prims.of_int (2))
                                (Prims.of_int (478)) (Prims.of_int (49)))))
               with
               | true ->
                   (match (split_conjunctions p)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (476))
                                              (Prims.of_int (2))
                                              (Prims.of_int (478))
                                              (Prims.of_int (49))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (476))
                                        (Prims.of_int (18))
                                        (Prims.of_int (476))
                                        (Prims.of_int (38))))))
                    with
                    | FStar_Tactics_Result.Success (a1, ps'1) ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'1
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (477))
                                          (Prims.of_int (2))
                                          (Prims.of_int (478))
                                          (Prims.of_int (49)))))
                         with
                         | true ->
                             (match (FStar_InteractiveHelpers_Base.print_dbg
                                       dbg
                                       (Prims.strcat "Conjuncts:\n"
                                          (FStar_InteractiveHelpers_Base.list_to_string
                                             FStar_Reflection_Builtins.term_to_string
                                             a1)))
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (477))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (478))
                                                        (Prims.of_int (49))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (477))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (477))
                                                  (Prims.of_int (74))))))
                              with
                              | FStar_Tactics_Result.Success (a2, ps'2) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'2
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (478))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (478))
                                                    (Prims.of_int (49)))))
                                   with
                                   | true ->
                                       (FStar_Tactics_Util.tryPick
                                          (is_equality_for_term dbg tm) a1)
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (478))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (478))
                                                     (Prims.of_int (49)))))))
                              | FStar_Tactics_Result.Failed (e, ps'2) ->
                                  FStar_Tactics_Result.Failed (e, ps'2)))
                    | FStar_Tactics_Result.Failed (e, ps'1) ->
                        FStar_Tactics_Result.Failed (e, ps'1)))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (find_equality_from_post :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.bv ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.typ ->
              FStar_InteractiveHelpers_Effectful.effect_info ->
                FStar_Reflection_Data.term_view Prims.list ->
                  FStar_Reflection_Data.term_view Prims.list ->
                    FStar_Tactics_Types.proofstate ->
                      (FStar_InteractiveHelpers_Base.genv *
                        FStar_Reflection_Types.term
                        FStar_Pervasives_Native.option)
                        FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun let_bv ->
          fun ret_value ->
            fun ret_type ->
              fun einfo ->
                fun parents ->
                  fun children ->
                    fun ps ->
                      match (FStar_InteractiveHelpers_Base.print_dbg dbg
                               "[> find_equality_from_post")
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (485))
                                          (Prims.of_int (2))
                                          (Prims.of_int (485))
                                          (Prims.of_int (44))))))
                      with
                      | FStar_Tactics_Result.Success (a, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (486))
                                            (Prims.of_int (2))
                                            (Prims.of_int (503))
                                            (Prims.of_int (27)))))
                           with
                           | true ->
                               (match (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                         ret_type)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (486))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (503))
                                                          (Prims.of_int (27))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (486))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (486))
                                                    (Prims.of_int (46))))))
                                with
                                | FStar_Tactics_Result.Success (a1, ps'1) ->
                                    (match FStar_Tactics_Types.tracepoint
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (488))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (503))
                                                      (Prims.of_int (27)))))
                                     with
                                     | true ->
                                         (match (FStar_InteractiveHelpers_Effectful.pre_post_to_propositions
                                                   dbg ge0
                                                   einfo.FStar_InteractiveHelpers_Effectful.ei_type
                                                   ret_value
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Reflection_Derived.mk_binder
                                                         let_bv)) a1
                                                   einfo.FStar_InteractiveHelpers_Effectful.ei_pre
                                                   einfo.FStar_InteractiveHelpers_Effectful.ei_post
                                                   parents children)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (27))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (489))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (490))
                                                              (Prims.of_int (78))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a2, ps'2) ->
                                              (match FStar_Tactics_Types.tracepoint
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (488))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (503))
                                                                (Prims.of_int (27)))))
                                               with
                                               | true ->
                                                   ((match a2 with
                                                     | (ge1, uu___,
                                                        post_prop) ->
                                                         (fun ps1 ->
                                                            match (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Computed post: "
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Reflection_Builtins.term_to_string
                                                                    post_prop)))
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (79))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a3, ps'3) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (27)))))
                                                                 with
                                                                 | true ->
                                                                    (match 
                                                                    (match post_prop
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    s))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    p ->
                                                                    find_subequality
                                                                    dbg tm p)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (27))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (41))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (27)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (ge0,
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tm1 ->
                                                                    (ge1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    tm1)))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (27))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
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
                                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (488))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (503))
                                                                 (Prims.of_int (27)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e, ps'2) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'2)))
                                | FStar_Tactics_Result.Failed (e, ps'1) ->
                                    FStar_Tactics_Result.Failed (e, ps'1)))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')
let rec (find_context_equality_aux :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.bv FStar_Pervasives_Native.option ->
          FStar_Reflection_Data.term_view Prims.list ->
            FStar_Reflection_Data.term_view Prims.list ->
              FStar_Tactics_Types.proofstate ->
                (FStar_InteractiveHelpers_Base.genv *
                  FStar_Reflection_Types.term FStar_Pervasives_Native.option)
                  FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun opt_bv ->
          fun parents ->
            fun children ->
              match parents with
              | [] ->
                  (fun s ->
                     FStar_Tactics_Result.Success
                       ((ge0, FStar_Pervasives_Native.None), s))
              | tv::parents' ->
                  (fun ps ->
                     match match match match match match match match 
                                                                 (FStar_Tactics_Builtins.pack
                                                                    tv)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (6))))))
                                                               with
                                                               | FStar_Tactics_Result.Success
                                                                   (a, ps')
                                                                   ->
                                                                   (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_to_string
                                                                    a),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (51))))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e, ps')
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a, ps') ->
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
                                                                    "- parent: "
                                                                    a),
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
                                                   | FStar_Tactics_Result.Success
                                                       (a, ps') ->
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
                                                                  "\n" a),
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
                                             | FStar_Tactics_Result.Success
                                                 (a, ps') ->
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
                                                            (FStar_Reflection_Builtins.term_to_string
                                                               tm) a),
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
                                       | FStar_Tactics_Result.Success
                                           (a, ps') ->
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
                                                  ((Prims.strcat "- term  : "
                                                      a),
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
                                 | FStar_Tactics_Result.Success (a, ps') ->
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
                                                "[> find_context_equality:\n"
                                                a),
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
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (522))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (524))
                                                 (Prims.of_int (52)))))
                                with
                                | true ->
                                    (FStar_InteractiveHelpers_Base.print_dbg
                                       dbg a)
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (522))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (524))
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
                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (526))
                                           (Prims.of_int (4))
                                           (Prims.of_int (550))
                                           (Prims.of_int (79)))))
                          with
                          | true ->
                              ((match tv with
                                | FStar_Reflection_Data.Tv_Let
                                    (uu___, uu___1, bv', def, uu___2) ->
                                    (fun ps1 ->
                                       match (FStar_InteractiveHelpers_Base.print_dbg
                                                dbg "Is Tv_Let")
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (528))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (528))
                                                           (Prims.of_int (31))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a1, ps'1) ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (529))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (549))
                                                             (Prims.of_int (11)))))
                                            with
                                            | true ->
                                                (match (FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                          dbg
                                                          ge0.FStar_InteractiveHelpers_Base.env
                                                          def)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (54))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a2, ps'2) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11)))))
                                                      with
                                                      | true ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11)))))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11)))))
                                                                with
                                                                | true ->
                                                                    (if
                                                                    (match opt_bv
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tm_bv ->
                                                                    FStar_InteractiveHelpers_Base.bv_eq
                                                                    tm_bv bv'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> false)
                                                                    &&
                                                                    (FStar_InteractiveHelpers_ExploreTerm.effect_type_is_pure
                                                                    (a2.FStar_InteractiveHelpers_Effectful.einfo).FStar_InteractiveHelpers_Effectful.ei_type)
                                                                    then
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge0,
                                                                    (FStar_Pervasives_Native.Some
                                                                    def)), s))
                                                                    else
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv'))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (41))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (90)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (find_equality_from_post
                                                                    dbg ge0
                                                                    tm bv' a3
                                                                    (FStar_Reflection_Derived.type_of_bv
                                                                    bv')
                                                                    a2.FStar_InteractiveHelpers_Effectful.einfo
                                                                    parents
                                                                    children)
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (544))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (90))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (546))
                                                                    (Prims.of_int (66))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (90)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (ge1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    p)), s))
                                                                    | (uu___4,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    find_context_equality_aux
                                                                    dbg ge0
                                                                    tm opt_bv
                                                                    parents'
                                                                    (tv ::
                                                                    children)))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (548))
                                                                    (Prims.of_int (90)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
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
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (537))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11)))))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e, ps'2) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'2)))
                                       | FStar_Tactics_Result.Failed
                                           (e, ps'1) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'1))
                                | uu___ ->
                                    find_context_equality_aux dbg ge0 tm
                                      opt_bv parents' (tv :: children)))
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (526))
                                            (Prims.of_int (4))
                                            (Prims.of_int (550))
                                            (Prims.of_int (79)))))))
                     | FStar_Tactics_Result.Failed (e, ps') ->
                         FStar_Tactics_Result.Failed (e, ps'))
let (find_context_equality :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Data.term_view Prims.list ->
          FStar_Reflection_Data.term_view Prims.list ->
            FStar_Tactics_Types.proofstate ->
              (FStar_InteractiveHelpers_Base.genv *
                FStar_Reflection_Types.term FStar_Pervasives_Native.option)
                FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun parents ->
          fun children ->
            fun ps ->
              match match (FStar_Tactics_Builtins.inspect tm)
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (554))
                                              (Prims.of_int (4))
                                              (Prims.of_int (556))
                                              (Prims.of_int (15))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (554))
                                        (Prims.of_int (10))
                                        (Prims.of_int (554))
                                        (Prims.of_int (20))))))
                    with
                    | FStar_Tactics_Result.Success (a, ps') ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (554))
                                          (Prims.of_int (4))
                                          (Prims.of_int (556))
                                          (Prims.of_int (15)))))
                         with
                         | true ->
                             ((match a with
                               | FStar_Reflection_Data.Tv_Var bv ->
                                   (fun s ->
                                      FStar_Tactics_Result.Success
                                        ((FStar_Pervasives_Native.Some bv),
                                          s))
                               | uu___ ->
                                   (fun s ->
                                      FStar_Tactics_Result.Success
                                        (FStar_Pervasives_Native.None, s))))
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (554))
                                           (Prims.of_int (4))
                                           (Prims.of_int (556))
                                           (Prims.of_int (15)))))))
                    | FStar_Tactics_Result.Failed (e, ps') ->
                        FStar_Tactics_Result.Failed (e, ps')
              with
              | FStar_Tactics_Result.Success (a, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (558)) (Prims.of_int (2))
                                    (Prims.of_int (558)) (Prims.of_int (62)))))
                   with
                   | true ->
                       (find_context_equality_aux dbg ge0 tm a parents
                          children)
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (558)) (Prims.of_int (2))
                                     (Prims.of_int (558)) (Prims.of_int (62)))))))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
let rec (replace_term_in :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun from_term ->
      fun to_term ->
        fun tm ->
          if FStar_Reflection_Builtins.term_eq from_term tm
          then fun s -> FStar_Tactics_Result.Success (to_term, s)
          else
            (fun ps ->
               match (FStar_Tactics_Builtins.inspect tm)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (564)) (Prims.of_int (8))
                                   (Prims.of_int (564)) (Prims.of_int (18))))))
               with
               | FStar_Tactics_Result.Success (a, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (564)) (Prims.of_int (2))
                                     (Prims.of_int (604)) (Prims.of_int (6)))))
                    with
                    | true ->
                        ((match a with
                          | FStar_Reflection_Data.Tv_Var uu___1 ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_BVar uu___1 ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_FVar uu___1 ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_App (hd, (a1, qual)) ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          a1)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (567))
                                                     (Prims.of_int (52))))))
                                 with
                                 | FStar_Tactics_Result.Success (a2, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (568))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (569))
                                                       (Prims.of_int (32)))))
                                      with
                                      | true ->
                                          (match (replace_term_in dbg
                                                    from_term to_term hd)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (568))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (32))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (568))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (568))
                                                               (Prims.of_int (54))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a3, ps'2) ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (569))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (569))
                                                                 (Prims.of_int (32)))))
                                                with
                                                | true ->
                                                    (FStar_Tactics_Builtins.pack
                                                       (FStar_Reflection_Data.Tv_App
                                                          (a3, (a2, qual))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (569))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (569))
                                                                  (Prims.of_int (32)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e, ps'2) ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'2)))
                                 | FStar_Tactics_Result.Failed (e, ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1))
                          | FStar_Reflection_Data.Tv_Abs (br, body) ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          body)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (571))
                                                     (Prims.of_int (16))
                                                     (Prims.of_int (571))
                                                     (Prims.of_int (58))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (572))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (572))
                                                       (Prims.of_int (26)))))
                                      with
                                      | true ->
                                          (FStar_Tactics_Builtins.pack
                                             (FStar_Reflection_Data.Tv_Abs
                                                (br, a1)))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (572))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (572))
                                                        (Prims.of_int (26)))))))
                                 | FStar_Tactics_Result.Failed (e, ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1))
                          | FStar_Reflection_Data.Tv_Arrow (br, c0) ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_Type () ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_Refine (bv, ref) ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          ref)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (576))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (576))
                                                     (Prims.of_int (56))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (577))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (577))
                                                       (Prims.of_int (28)))))
                                      with
                                      | true ->
                                          (FStar_Tactics_Builtins.pack
                                             (FStar_Reflection_Data.Tv_Refine
                                                (bv, a1)))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (577))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (577))
                                                        (Prims.of_int (28)))))))
                                 | FStar_Tactics_Result.Failed (e, ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1))
                          | FStar_Reflection_Data.Tv_Const uu___1 ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_Uvar (uu___1, uu___2) ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))
                          | FStar_Reflection_Data.Tv_Let
                              (recf, attrs, bv, def, body) ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          def)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (581))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (581))
                                                     (Prims.of_int (56))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (582))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (583))
                                                       (Prims.of_int (42)))))
                                      with
                                      | true ->
                                          (match (replace_term_in dbg
                                                    from_term to_term body)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (583))
                                                                    (Prims.of_int (42))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (582))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (582))
                                                               (Prims.of_int (58))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a2, ps'2) ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (583))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (583))
                                                                 (Prims.of_int (42)))))
                                                with
                                                | true ->
                                                    (FStar_Tactics_Builtins.pack
                                                       (FStar_Reflection_Data.Tv_Let
                                                          (recf, attrs, bv,
                                                            a1, a2)))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (583))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (583))
                                                                  (Prims.of_int (42)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e, ps'2) ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'2)))
                                 | FStar_Tactics_Result.Failed (e, ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1))
                          | FStar_Reflection_Data.Tv_Match
                              (scrutinee, ret_opt, branches) ->
                              (fun ps1 ->
                                 match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (588))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (18))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (592))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (594))
                                                  (Prims.of_int (48)))))
                                 with
                                 | true ->
                                     (match (replace_term_in dbg from_term
                                               to_term scrutinee)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps1
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (18))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (592))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (594))
                                                                (Prims.of_int (48))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (592))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (592))
                                                          (Prims.of_int (68))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1, ps'1) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (593))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (594))
                                                            (Prims.of_int (48)))))
                                           with
                                           | true ->
                                               (match (FStar_Tactics_Util.map
                                                         (fun br ->
                                                            fun ps2 ->
                                                              match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (19)))))
                                                              with
                                                              | true ->
                                                                  ((match br
                                                                    with
                                                                    | 
                                                                    (pat,
                                                                    body) ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (replace_term_in
                                                                    dbg
                                                                    from_term
                                                                    to_term
                                                                    body)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (60))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (18)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((pat,
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (18))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))))
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (19)))))))
                                                         branches)
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (48))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (47))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a2, ps'2) ->
                                                    (match FStar_Tactics_Types.tracepoint
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (48)))))
                                                     with
                                                     | true ->
                                                         (FStar_Tactics_Builtins.pack
                                                            (FStar_Reflection_Data.Tv_Match
                                                               (a1, ret_opt,
                                                                 a2)))
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (594))
                                                                    (Prims.of_int (48)))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e, ps'2) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'2)))
                                      | FStar_Tactics_Result.Failed (e, ps'1)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'1)))
                          | FStar_Reflection_Data.Tv_AscribedT (e, ty, tac)
                              ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          e)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (596))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (596))
                                                     (Prims.of_int (52))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (597))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (598))
                                                       (Prims.of_int (34)))))
                                      with
                                      | true ->
                                          (match (replace_term_in dbg
                                                    from_term to_term ty)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (34))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (597))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (597))
                                                               (Prims.of_int (54))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a2, ps'2) ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'2
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (598))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (598))
                                                                 (Prims.of_int (34)))))
                                                with
                                                | true ->
                                                    (FStar_Tactics_Builtins.pack
                                                       (FStar_Reflection_Data.Tv_AscribedT
                                                          (a1, a2, tac)))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (598))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (598))
                                                                  (Prims.of_int (34)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e1, ps'2) ->
                                               FStar_Tactics_Result.Failed
                                                 (e1, ps'2)))
                                 | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                     FStar_Tactics_Result.Failed (e1, ps'1))
                          | FStar_Reflection_Data.Tv_AscribedC (e, c, tac) ->
                              (fun ps1 ->
                                 match (replace_term_in dbg from_term to_term
                                          e)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (600))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (600))
                                                     (Prims.of_int (52))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (601))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (601))
                                                       (Prims.of_int (32)))))
                                      with
                                      | true ->
                                          (FStar_Tactics_Builtins.pack
                                             (FStar_Reflection_Data.Tv_AscribedC
                                                (a1, c, tac)))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (601))
                                                        (Prims.of_int (32)))))))
                                 | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                     FStar_Tactics_Result.Failed (e1, ps'1))
                          | uu___1 ->
                              (fun s -> FStar_Tactics_Result.Success (tm, s))))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (564)) (Prims.of_int (2))
                                      (Prims.of_int (604)) (Prims.of_int (6)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let rec (strip_implicit_parameters :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun tm ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (608)) (Prims.of_int (8))
                          (Prims.of_int (608)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (608)) (Prims.of_int (2))
                            (Prims.of_int (611)) (Prims.of_int (11)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_App (hd, (a1, qualif)) ->
                     if FStar_Reflection_Data.uu___is_Q_Implicit qualif
                     then strip_implicit_parameters hd
                     else (fun s -> FStar_Tactics_Result.Success (tm, s))
                 | uu___ -> (fun s -> FStar_Tactics_Result.Success (tm, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (608)) (Prims.of_int (2))
                             (Prims.of_int (611)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (unfold_in_assert_or_assume :
  Prims.bool ->
    FStar_Reflection_Types.term exploration_result ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ares ->
      fun ps ->
        match (FStar_InteractiveHelpers_Base.print_dbg dbg
                 (Prims.strcat "[> unfold_in_assert_or_assume:\n"
                    (FStar_Reflection_Builtins.term_to_string ares.res)))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (615)) (Prims.of_int (2))
                            (Prims.of_int (615)) (Prims.of_int (78))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (618)) (Prims.of_int (2))
                              (Prims.of_int (749)) (Prims.of_int (30)))))
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
                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (618))
                                               (Prims.of_int (2))
                                               (Prims.of_int (749))
                                               (Prims.of_int (30))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (619))
                                         (Prims.of_int (4))
                                         (Prims.of_int (619))
                                         (Prims.of_int (68))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (621)) (Prims.of_int (2))
                                   (Prims.of_int (749)) (Prims.of_int (30)))))
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
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (618))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (749))
                                                                (Prims.of_int (30))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (619))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (619))
                                                          (Prims.of_int (68))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (621))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (749))
                                                    (Prims.of_int (30))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (622))
                                              (Prims.of_int (4))
                                              (Prims.of_int (625))
                                              (Prims.of_int (93))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (635))
                                        (Prims.of_int (2))
                                        (Prims.of_int (749))
                                        (Prims.of_int (30)))))
                       with
                       | true ->
                           (match match (FStar_InteractiveHelpers_Base.print_dbg
                                           dbg
                                           (Prims.strcat "Assertion: "
                                              (FStar_Reflection_Builtins.term_to_string
                                                 ares.res)))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (93))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (635))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (749))
                                                                  (Prims.of_int (30))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (636))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (663))
                                                            (Prims.of_int (27))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (636))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (636))
                                                      (Prims.of_int (67))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (637))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (663))
                                                        (Prims.of_int (27)))))
                                       with
                                       | true ->
                                           (match (is_eq dbg ares.res)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'1
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (27))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (637))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (637))
                                                                (Prims.of_int (28))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2, ps'2) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (637))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (663))
                                                                  (Prims.of_int (27)))))
                                                 with
                                                 | true ->
                                                     ((match a2 with
                                                       | FStar_Pervasives_Native.Some
                                                           (kd, l, r) ->
                                                           (fun ps1 ->
                                                              match (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The assertion is an equality")
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (50))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (11)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    (match 
                                                                    (find_focused_term
                                                                    dbg false
                                                                    ares.ge
                                                                    ares.parents
                                                                    ares.tgt_comp
                                                                    l)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (11))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (40))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (11)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Found focused term in left operand:"
                                                                    (Prims.strcat
                                                                    "\n- left   : "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    l)
                                                                    (Prims.strcat
                                                                    "\n- right  : "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    r)
                                                                    (Prims.strcat
                                                                    "\n- focused: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    res.res))))))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (64))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (29)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((l, res,
                                                                    ((fun t
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((mk_eq
                                                                    kd t r),
                                                                    s))),
                                                                    true),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (29))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (find_focused_term
                                                                    dbg false
                                                                    ares.ge
                                                                    ares.parents
                                                                    ares.tgt_comp
                                                                    r)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (649))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (658))
                                                                    (Prims.of_int (89)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Found focused term in right operand:"
                                                                    (Prims.strcat
                                                                    "\n- left   : "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    l)
                                                                    (Prims.strcat
                                                                    "\n- right  : "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    r)
                                                                    (Prims.strcat
                                                                    "\n- focused: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    res.res))))))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (654))
                                                                    (Prims.of_int (58))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (32)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((r, res,
                                                                    ((fun t
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((mk_eq
                                                                    kd l t),
                                                                    s))),
                                                                    false),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (32))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6))
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: could not find a focused term in the assert"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (658))
                                                                    (Prims.of_int (89)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (11)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'3)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                       | FStar_Pervasives_Native.None
                                                           ->
                                                           (fun ps1 ->
                                                              match (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The assertion is not an equality")
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (54))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (93)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    (match 
                                                                    (find_focused_term
                                                                    dbg false
                                                                    ares.ge
                                                                    ares.parents
                                                                    ares.tgt_comp
                                                                    ares.res)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (93))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (39))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((ares.res),
                                                                    res,
                                                                    (fun x ->
                                                                    fun s1 ->
                                                                    FStar_Tactics_Result.Success
                                                                    (x, s1)),
                                                                    true), s))
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: could not find a focused term in the assert"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (39)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'3)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (637))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (663))
                                                                   (Prims.of_int (27)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'2) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'2)))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1)
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (635))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (749))
                                                  (Prims.of_int (30)))))
                                 with
                                 | true ->
                                     ((match a1 with
                                       | (subterm, unf_res, rebuild,
                                          insert_before) ->
                                           (fun ps1 ->
                                              match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (665))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (749))
                                                               (Prims.of_int (30)))))
                                              with
                                              | true ->
                                                  (match (FStar_InteractiveHelpers_Base.print_dbg
                                                            dbg
                                                            (Prims.strcat
                                                               "Found subterm in assertion/assumption:\n"
                                                               (Prims.strcat
                                                                  "- subterm: "
                                                                  (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    subterm)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "- focused term: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    unf_res.res)))))))
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (65))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a2, ps'2) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'2
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_Tactics_Builtins.inspect
                                                                    unf_res.res)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (36))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                  with
                                                                  | true ->
                                                                    (match 
                                                                    (match a3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier: "
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (80))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    (ares.ge).FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm)
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (676))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Normalized subterm: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a5)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (70))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((ares.ge),
                                                                    (FStar_Pervasives_Native.Some
                                                                    a5)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (28))))))))
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
                                                                    (e, ps'5))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | 
                                                                    uu___ ->
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (match a3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    bv ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a local variable: "
                                                                    (FStar_Reflection_Derived.bv_to_string
                                                                    bv)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (84))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (17)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    (FStar_InteractiveHelpers_Base.genv_get
                                                                    ares.ge
                                                                    bv))
                                                                    then
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: can't unfold a variable locally introduced in an assertion"
                                                                    else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((), s)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (106))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (17)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    bv),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (17))))))))
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
                                                                    (e, ps'4))
                                                                    | 
                                                                    uu___1 ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is an arbitrary term: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    unf_res.res)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (96))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (14)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (14))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (14))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (find_context_equality
                                                                    dbg
                                                                    ares.ge
                                                                    unf_res.res
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    ares.parents)
                                                                    [])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (79))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | (ge1,
                                                                    eq_tm) ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (match 
                                                                    (a4,
                                                                    (match eq_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1
                                                                    | 
                                                                    uu___1 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    bv,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    subterm
                                                                    [
                                                                    (bv,
                                                                    eq_tm1)])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (81))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (81)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    a6),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (81))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (replace_term_in
                                                                    dbg
                                                                    unf_res.res
                                                                    eq_tm1
                                                                    subterm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (82))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (82)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Pervasives_Native.Some
                                                                    a6),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (82))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6))
                                                                    | 
                                                                    uu___1 ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    (FStar_Pervasives_Native.None,
                                                                    s)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (19))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge1,
                                                                    a6),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19)))))))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (19))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (ge1,
                                                                    opt_unf_tm)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (match opt_unf_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    unf_tm ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge1,
                                                                    unf_tm),
                                                                    s))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    (strip_implicit_parameters
                                                                    unf_res.res)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (65))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (65))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (65)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    a5)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (65)))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (42)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier with implicit parameters: "
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (41))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21)))))
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
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (729))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (79))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "Normalized subterm: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a7)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (72))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge1,
                                                                    a7),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (21))))))))
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
                                                                    (e, ps'7))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6))
                                                                    | uu___
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.mfail
                                                                    (Prims.strcat
                                                                    "unfold_in_assert_or_assume: "
                                                                    (Prims.strcat
                                                                    "couldn't find equalities with which to rewrite: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    unf_res.res)))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (42)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (9))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | (ge2,
                                                                    unf_tm)
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (rebuild
                                                                    unf_tm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (740))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (740))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.prettify_term
                                                                    dbg a6)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (51))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "-> Final assertion:\n"
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    a7)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (71))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
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
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (94))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    FStar_Pervasives_Native.None
                                                                    (if
                                                                    insert_before
                                                                    then
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    [a7] []
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    [] 
                                                                    [a7]))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (94))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (79))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a9
                                                                    with
                                                                    | (ge3,
                                                                    asserts)
                                                                    ->
                                                                    FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    asserts))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9))))
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
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (30)))))))
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
                                                         (e, ps'2)))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (635))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (749))
                                                   (Prims.of_int (30)))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (pp_unfold_in_assert_or_assume :
  Prims.bool ->
    unit ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               (fun ps ->
                  match (find_focused_assert_in_current_goal dbg)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (755))
                                      (Prims.of_int (14))
                                      (Prims.of_int (755))
                                      (Prims.of_int (53))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (756))
                                        (Prims.of_int (4))
                                        (Prims.of_int (757))
                                        (Prims.of_int (16)))))
                       with
                       | true ->
                           (match (unfold_in_assert_or_assume dbg a)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (756))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (757))
                                                      (Prims.of_int (16))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (756))
                                                (Prims.of_int (4))
                                                (Prims.of_int (756))
                                                (Prims.of_int (38))))))
                            with
                            | FStar_Tactics_Result.Success (a1, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (757))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (757))
                                                  (Prims.of_int (16)))))
                                 with
                                 | true ->
                                     (end_proof ())
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (757))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (757))
                                                   (Prims.of_int (16)))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
        (fun uu___1 ->
           match uu___1 with
           | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
               (fun ps ->
                  match (FStar_InteractiveHelpers_Output.printout_failure msg)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (758))
                                      (Prims.of_int (29))
                                      (Prims.of_int (758))
                                      (Prims.of_int (49))))))
                  with
                  | FStar_Tactics_Result.Success (a, ps') ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (758))
                                        (Prims.of_int (51))
                                        (Prims.of_int (758))
                                        (Prims.of_int (63)))))
                       with
                       | true ->
                           (end_proof ())
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "experimental/FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (758))
                                         (Prims.of_int (51))
                                         (Prims.of_int (758))
                                         (Prims.of_int (63)))))))
                  | FStar_Tactics_Result.Failed (e, ps') ->
                      FStar_Tactics_Result.Failed (e, ps'))
           | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_unfold_in_assert_or_assume"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2
                pp_unfold_in_assert_or_assume) FStar_Syntax_Embeddings.e_bool
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)