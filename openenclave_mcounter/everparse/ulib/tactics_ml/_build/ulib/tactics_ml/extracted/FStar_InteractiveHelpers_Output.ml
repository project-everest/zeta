open Prims
let rec _split_subst_at_bv :
  'a .
    FStar_Reflection_Types.bv ->
      (FStar_Reflection_Types.bv * 'a) Prims.list ->
        ((FStar_Reflection_Types.bv * 'a) Prims.list *
          (FStar_Reflection_Types.bv * 'a) Prims.list)
  =
  fun b ->
    fun subst ->
      match subst with
      | [] -> ([], [])
      | (src, tgt)::subst' ->
          if FStar_InteractiveHelpers_Base.bv_eq b src
          then ([], subst')
          else
            (let uu___1 = _split_subst_at_bv b subst' in
             match uu___1 with | (s1, s2) -> (((src, tgt) :: s1), s2))
let (subst_shadowed_with_abs_in_assertions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.bv FStar_Pervasives_Native.option ->
        FStar_InteractiveHelpers_Propositions.assertions ->
          FStar_Tactics_Types.proofstate ->
            (FStar_InteractiveHelpers_Base.genv *
              FStar_InteractiveHelpers_Propositions.assertions)
              FStar_Tactics_Result.__result)
  =
  fun dbg ->
    fun ge ->
      fun shadowed_bv ->
        fun as1 ->
          fun ps ->
            match (FStar_InteractiveHelpers_Base.print_dbg dbg
                     (Prims.strcat "subst_shadowed_with_abs_in_assertions:\n"
                        (FStar_InteractiveHelpers_Base.genv_to_string ge)))
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                (Prims.of_int (44)) (Prims.of_int (2))
                                (Prims.of_int (44)) (Prims.of_int (80))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                  (Prims.of_int (46)) (Prims.of_int (2))
                                  (Prims.of_int (73)) (Prims.of_int (31)))))
                 with
                 | true ->
                     (match (FStar_InteractiveHelpers_Base.generate_shadowed_subst
                               ge)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                                (Prims.of_int (46))
                                                (Prims.of_int (2))
                                                (Prims.of_int (73))
                                                (Prims.of_int (31))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.Output.fst"
                                          (Prims.of_int (46))
                                          (Prims.of_int (19))
                                          (Prims.of_int (46))
                                          (Prims.of_int (45))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                            (Prims.of_int (46))
                                            (Prims.of_int (2))
                                            (Prims.of_int (73))
                                            (Prims.of_int (31)))))
                           with
                           | true ->
                               ((match a1 with
                                 | (ge1, subst) ->
                                     (fun ps1 ->
                                        match (FStar_Tactics_Util.map
                                                 (fun uu___ ->
                                                    match uu___ with
                                                    | (src, tgt) ->
                                                        (fun ps2 ->
                                                           match (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    tgt))
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (64))))))
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a2, ps'2) ->
                                                               (match 
                                                                  FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (64)))))
                                                                with
                                                                | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((src,
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (64))))))))
                                                           | FStar_Tactics_Result.Failed
                                                               (e, ps'2) ->
                                                               FStar_Tactics_Result.Failed
                                                                 (e, ps'2)))
                                                 subst)
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                                            (Prims.of_int (47))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (47))
                                                            (Prims.of_int (71))))))
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a2, ps'2) ->
                                            (match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'2
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (53))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (73))
                                                              (Prims.of_int (31)))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (19))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (57))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (73))
                                                                   (Prims.of_int (31)))))
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
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                       with
                                                       | true ->
                                                           (match (if dbg
                                                                   then
                                                                    fun ps2
                                                                    ->
                                                                    match 
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- pre_subst:\n"
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___ ->
                                                                    match uu___
                                                                    with
                                                                    | 
                                                                    (x, y) ->
                                                                    Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    (FStar_InteractiveHelpers_Base.abv_to_string
                                                                    x)
                                                                    (Prims.strcat
                                                                    " -> "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    y) ")\n"))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    shadowed_bv
                                                                    then
                                                                    FStar_Pervasives_Native.fst
                                                                    (_split_subst_at_bv
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    shadowed_bv)
                                                                    a2)
                                                                    else a2)))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- post_subst:\n"
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___ ->
                                                                    match uu___
                                                                    with
                                                                    | 
                                                                    (x, y) ->
                                                                    Prims.strcat
                                                                    "("
                                                                    (Prims.strcat
                                                                    (FStar_InteractiveHelpers_Base.abv_to_string
                                                                    x)
                                                                    (Prims.strcat
                                                                    " -> "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    y) ")\n"))))
                                                                    a2))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                   else
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((), s)))
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
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
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (19))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a3, ps'3) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                 with
                                                                 | true ->
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Util.map
                                                                    (fun t ->
                                                                    FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    t
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    shadowed_bv
                                                                    then
                                                                    FStar_Pervasives_Native.fst
                                                                    (_split_subst_at_bv
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    shadowed_bv)
                                                                    a2)
                                                                    else a2))
                                                                    as1.FStar_InteractiveHelpers_Propositions.pres)
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (13))
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Util.map
                                                                    (fun t ->
                                                                    FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    t a2)
                                                                    as1.FStar_InteractiveHelpers_Propositions.posts)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (39))))))
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((ge1,
                                                                    (FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    a4 a5)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))))))))
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
                                                            | FStar_Tactics_Result.Failed
                                                                (e, ps'3) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'3)))))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps'2) ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps'2))))
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (46))
                                             (Prims.of_int (2))
                                             (Prims.of_int (73))
                                             (Prims.of_int (31)))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
let (string_to_printout : Prims.string -> Prims.string -> Prims.string) =
  fun prefix ->
    fun data ->
      Prims.strcat prefix (Prims.strcat ":\n" (Prims.strcat data "\n"))
let (term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun prefix ->
      fun t ->
        fun ps ->
          match (FStar_InteractiveHelpers_ExploreTerm.abs_free_in ge t)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (87)) (Prims.of_int (12))
                              (Prims.of_int (87)) (Prims.of_int (28))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                (Prims.of_int (88)) (Prims.of_int (2))
                                (Prims.of_int (92)) (Prims.of_int (46)))))
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
                                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (88))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (92))
                                                 (Prims.of_int (46))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.Output.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (20))
                                           (Prims.of_int (88))
                                           (Prims.of_int (46))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (89)) (Prims.of_int (2))
                                     (Prims.of_int (92)) (Prims.of_int (46)))))
                    with
                    | true ->
                        (match (FStar_Tactics_Util.map
                                  (fun bv ->
                                     FStar_Tactics_Builtins.pack
                                       (FStar_Reflection_Data.Tv_Var bv)) a)
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
                                                               "experimental/FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (88))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (46))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (88))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (88))
                                                         (Prims.of_int (46))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                                   (Prims.of_int (89))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (92))
                                                   (Prims.of_int (46))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (89))
                                             (Prims.of_int (18))
                                             (Prims.of_int (89))
                                             (Prims.of_int (54))))))
                         with
                         | FStar_Tactics_Result.Success (a1, ps'1) ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (90))
                                               (Prims.of_int (2))
                                               (Prims.of_int (92))
                                               (Prims.of_int (46)))))
                              with
                              | true ->
                                  (match (FStar_Tactics_Derived.mk_abs
                                            (FStar_List_Tot_Base.map
                                               FStar_Reflection_Derived.mk_binder
                                               a) t)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                                             (Prims.of_int (90))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (92))
                                                             (Prims.of_int (46))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Output.fst"
                                                       (Prims.of_int (90))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (90))
                                                       (Prims.of_int (30))))))
                                   with
                                   | FStar_Tactics_Result.Success (a2, ps'2)
                                       ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (46)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((string_to_printout prefix
                                                  (FStar_Reflection_Builtins.term_to_string
                                                     (FStar_Reflection_Derived.mk_e_app
                                                        a2 a1))),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'2
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                                            (Prims.of_int (92))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (92))
                                                            (Prims.of_int (46))))))))
                                   | FStar_Tactics_Result.Failed (e, ps'2) ->
                                       FStar_Tactics_Result.Failed (e, ps'2)))
                         | FStar_Tactics_Result.Failed (e, ps'1) ->
                             FStar_Tactics_Result.Failed (e, ps'1))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let (opt_term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun prefix ->
      fun t ->
        match t with
        | FStar_Pervasives_Native.Some t' -> term_to_printout ge prefix t'
        | FStar_Pervasives_Native.None ->
            (fun s ->
               FStar_Tactics_Result.Success
                 ((string_to_printout prefix ""), s))
let (proposition_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_InteractiveHelpers_Propositions.proposition ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result)
  = fun ge -> fun prefix -> fun p -> term_to_printout ge prefix p
let (propositions_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_InteractiveHelpers_Propositions.proposition Prims.list ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result)
  =
  fun ge ->
    fun prefix ->
      fun pl ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (104)) (Prims.of_int (4))
                                 (Prims.of_int (105)) (Prims.of_int (40))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range
                           "experimental/FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (107)) (Prims.of_int (2))
                           (Prims.of_int (113)) (Prims.of_int (5)))))
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
                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (104))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (105))
                                                  (Prims.of_int (40))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                            (Prims.of_int (107))
                                            (Prims.of_int (2))
                                            (Prims.of_int (113))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Output.fst"
                                      (Prims.of_int (107))
                                      (Prims.of_int (12))
                                      (Prims.of_int (107))
                                      (Prims.of_int (85))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                (Prims.of_int (108)) (Prims.of_int (2))
                                (Prims.of_int (113)) (Prims.of_int (5)))))
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
                                                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (104))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (105))
                                                                   (Prims.of_int (40))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                                             (Prims.of_int (107))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (113))
                                                             (Prims.of_int (5))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Output.fst"
                                                       (Prims.of_int (107))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (107))
                                                       (Prims.of_int (85))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (108))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (113))
                                                 (Prims.of_int (5))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "experimental/FStar.InteractiveHelpers.Output.fst"
                                           (Prims.of_int (109))
                                           (Prims.of_int (4))
                                           (Prims.of_int (110))
                                           (Prims.of_int (33))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "experimental/FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (112)) (Prims.of_int (2))
                                     (Prims.of_int (113)) (Prims.of_int (5)))))
                    with
                    | true ->
                        (match (FStar_Tactics_Util.fold_left
                                  (fun s_i ->
                                     fun p ->
                                       fun ps1 ->
                                         match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                (Prims.of_int (109))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (109))
                                                                (Prims.of_int (18))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Output.fst"
                                                          (Prims.of_int (109))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (109))
                                                          (Prims.of_int (12)))))
                                         with
                                         | true ->
                                             ((match s_i with
                                               | (s, i) ->
                                                   (fun ps2 ->
                                                      match match match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (40)))))
                                                                  with
                                                                  | true ->
                                                                    (proposition_to_printout
                                                                    ge
                                                                    (Prims.strcat
                                                                    prefix
                                                                    (Prims.strcat
                                                                    ":prop"
                                                                    (Prims.string_of_int
                                                                    i))) p)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (40))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a, ps') ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
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
                                                                    s a),
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (33)))))
                                                           with
                                                           | true ->
                                                               FStar_Tactics_Result.Success
                                                                 ((a,
                                                                    (
                                                                    i +
                                                                    Prims.int_one)),
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (33))))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps') ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'))))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                 (Prims.of_int (109))
                                                                 (Prims.of_int (15))
                                                                 (Prims.of_int (109))
                                                                 (Prims.of_int (18))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.Output.fst"
                                                           (Prims.of_int (109))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (109))
                                                           (Prims.of_int (12)))))))
                                  ((string_to_printout
                                      (Prims.strcat prefix ":num")
                                      (Prims.string_of_int
                                         (FStar_List_Tot_Base.length pl))),
                                    Prims.int_zero) pl)
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (5))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (85))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "experimental/FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (108))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (113))
                                                               (Prims.of_int (5))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (109))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (110))
                                                         (Prims.of_int (33))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                                   (Prims.of_int (112))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (113))
                                                   (Prims.of_int (5))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (112))
                                             (Prims.of_int (15))
                                             (Prims.of_int (112))
                                             (Prims.of_int (47))))))
                         with
                         | FStar_Tactics_Result.Success (a, ps') ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (112))
                                               (Prims.of_int (2))
                                               (Prims.of_int (113))
                                               (Prims.of_int (5)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    (((match a with | (str, uu___) -> str)),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (112))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (113))
                                                  (Prims.of_int (5))))))))
                         | FStar_Tactics_Result.Failed (e, ps') ->
                             FStar_Tactics_Result.Failed (e, ps'))))
let (error_message_to_printout :
  Prims.string -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun prefix ->
    fun message ->
      let msg =
        match message with
        | FStar_Pervasives_Native.Some msg1 -> msg1
        | uu___ -> "" in
      string_to_printout (Prims.strcat prefix ":error") msg
type export_result =
  | ESuccess of FStar_InteractiveHelpers_Base.genv *
  FStar_InteractiveHelpers_Propositions.assertions 
  | EFailure of Prims.string 
let (uu___is_ESuccess : export_result -> Prims.bool) =
  fun projectee ->
    match projectee with | ESuccess (ge, a) -> true | uu___ -> false
let (__proj__ESuccess__item__ge :
  export_result -> FStar_InteractiveHelpers_Base.genv) =
  fun projectee -> match projectee with | ESuccess (ge, a) -> ge
let (__proj__ESuccess__item__a :
  export_result -> FStar_InteractiveHelpers_Propositions.assertions) =
  fun projectee -> match projectee with | ESuccess (ge, a) -> a
let (uu___is_EFailure : export_result -> Prims.bool) =
  fun projectee ->
    match projectee with | EFailure err -> true | uu___ -> false
let (__proj__EFailure__item__err : export_result -> Prims.string) =
  fun projectee -> match projectee with | EFailure err -> err
let (result_to_printout :
  Prims.string ->
    export_result ->
      FStar_Tactics_Types.proofstate ->
        Prims.string FStar_Tactics_Result.__result)
  =
  fun prefix ->
    fun res ->
      fun ps ->
        match FStar_Tactics_Types.tracepoint
                (FStar_Tactics_Types.set_proofstate_range
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.Output.fst"
                               (Prims.of_int (126)) (Prims.of_int (12))
                               (Prims.of_int (126)) (Prims.of_int (31))))))
                   (FStar_Range.prims_to_fstar_range
                      (Prims.mk_range
                         "experimental/FStar.InteractiveHelpers.Output.fst"
                         (Prims.of_int (130)) (Prims.of_int (2))
                         (Prims.of_int (142)) (Prims.of_int (50)))))
        with
        | true ->
            (match (match res with
                    | ESuccess (ge, a) ->
                        (fun s ->
                           FStar_Tactics_Result.Success
                             ((FStar_Pervasives_Native.None, ge,
                                (a.FStar_InteractiveHelpers_Propositions.pres),
                                (a.FStar_InteractiveHelpers_Propositions.posts)),
                               s))
                    | EFailure err ->
                        (fun ps1 ->
                           match match (FStar_Tactics_Builtins.top_env ())
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "experimental/FStar.InteractiveHelpers.Output.fst"
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (134))
                                                           (Prims.of_int (40))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.Output.fst"
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (40))))))
                                 with
                                 | FStar_Tactics_Result.Success (a, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "experimental/FStar.InteractiveHelpers.Output.fst"
                                                       (Prims.of_int (134))
                                                       (Prims.of_int (15))
                                                       (Prims.of_int (134))
                                                       (Prims.of_int (40)))))
                                      with
                                      | true ->
                                          FStar_Tactics_Result.Success
                                            ((FStar_InteractiveHelpers_Base.mk_init_genv
                                                a),
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "experimental/FStar.InteractiveHelpers.Output.fst"
                                                          (Prims.of_int (134))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (134))
                                                          (Prims.of_int (40))))))))
                                 | FStar_Tactics_Result.Failed (e, ps') ->
                                     FStar_Tactics_Result.Failed (e, ps')
                           with
                           | FStar_Tactics_Result.Success (a, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (135))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (135))
                                                 (Prims.of_int (26)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      (((FStar_Pervasives_Native.Some err),
                                         a, [], []),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (135))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (135))
                                                    (Prims.of_int (26))))))))
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
                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (126))
                                             (Prims.of_int (12))
                                             (Prims.of_int (126))
                                             (Prims.of_int (31))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (130))
                                       (Prims.of_int (2))
                                       (Prims.of_int (142))
                                       (Prims.of_int (50))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (131)) (Prims.of_int (4))
                                 (Prims.of_int (135)) (Prims.of_int (26))))))
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (130)) (Prims.of_int (2))
                                   (Prims.of_int (142)) (Prims.of_int (50)))))
                  with
                  | true ->
                      ((match a with
                        | (err, ge, pres, posts) ->
                            (fun ps1 ->
                               match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "experimental/FStar.InteractiveHelpers.Output.fst"
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (54))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                                (Prims.of_int (140))
                                                (Prims.of_int (2))
                                                (Prims.of_int (142))
                                                (Prims.of_int (50)))))
                               with
                               | true ->
                                   (match match (propositions_to_printout ge
                                                   (Prims.strcat prefix
                                                      ":pres") pres)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (54))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (50))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (69))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (140))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (140))
                                                              (Prims.of_int (69))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a1, ps'1) ->
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
                                                         (Prims.strcat
                                                            (Prims.strcat
                                                               prefix
                                                               ":BEGIN\n")
                                                            (error_message_to_printout
                                                               prefix err))
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
                                                          "experimental/FStar.InteractiveHelpers.Output.fst"
                                                          (Prims.of_int (141))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (142))
                                                          (Prims.of_int (50)))))
                                         with
                                         | true ->
                                             (match match (propositions_to_printout
                                                             ge
                                                             (Prims.strcat
                                                                prefix
                                                                ":posts")
                                                             posts)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (71))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (71))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a2, ps'2) ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
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
                                                                   a1 a2),
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
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
                                                          (e, ps'2)
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a2, ps'2) ->
                                                  (match FStar_Tactics_Types.tracepoint
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
                                                         ((Prims.strcat a2
                                                             (Prims.strcat
                                                                prefix
                                                                ":END\n%FIH:FSTAR_META:END%")),
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'2)))
                                    | FStar_Tactics_Result.Failed (e, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'1)))))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                    (Prims.of_int (130)) (Prims.of_int (2))
                                    (Prims.of_int (142)) (Prims.of_int (50)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let (printout_result :
  Prims.string ->
    export_result ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun prefix ->
    fun res ->
      fun ps ->
        match (result_to_printout prefix res)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (146)) (Prims.of_int (8))
                            (Prims.of_int (146)) (Prims.of_int (39))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (146)) (Prims.of_int (2))
                              (Prims.of_int (146)) (Prims.of_int (39)))))
             with
             | true ->
                 (FStar_Tactics_Builtins.print a)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "experimental/FStar.InteractiveHelpers.Output.fst"
                               (Prims.of_int (146)) (Prims.of_int (2))
                               (Prims.of_int (146)) (Prims.of_int (39)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let (printout_success :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_InteractiveHelpers_Propositions.assertions ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun ge -> fun a -> printout_result "ainfo" (ESuccess (ge, a))
let (printout_failure :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun err -> printout_result "ainfo" (EFailure err)
let (_debug_print_var :
  Prims.string ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun name ->
    fun t ->
      fun ps ->
        match (FStar_Tactics_Builtins.print
                 (Prims.strcat "_debug_print_var: "
                    (Prims.strcat name
                       (Prims.strcat ": "
                          (FStar_Reflection_Builtins.term_to_string t)))))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (157)) (Prims.of_int (2))
                            (Prims.of_int (157)) (Prims.of_int (63))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "experimental/FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (158)) (Prims.of_int (2))
                              (Prims.of_int (171)) (Prims.of_int (33)))))
             with
             | true ->
                 (match match match (FStar_Tactics_Builtins.top_env ())
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (33))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (158))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (160))
                                                              (Prims.of_int (11))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Output.fst"
                                                        (Prims.of_int (158))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (158))
                                                        (Prims.of_int (36))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (158))
                                                  (Prims.of_int (22))
                                                  (Prims.of_int (158))
                                                  (Prims.of_int (34))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (36)))))
                                   with
                                   | true ->
                                       (FStar_InteractiveHelpers_ExploreTerm.safe_tc
                                          a1 t)
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "experimental/FStar.InteractiveHelpers.Output.fst"
                                                     (Prims.of_int (158))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (158))
                                                     (Prims.of_int (36)))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (158))
                                              (Prims.of_int (8))
                                              (Prims.of_int (160))
                                              (Prims.of_int (11)))))
                             with
                             | true ->
                                 ((match a1 with
                                   | FStar_Pervasives_Native.Some ty ->
                                       FStar_Tactics_Builtins.print
                                         (Prims.strcat "type: "
                                            (FStar_Reflection_Builtins.term_to_string
                                               ty))
                                   | uu___ ->
                                       (fun s ->
                                          FStar_Tactics_Result.Success
                                            ((), s))))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "experimental/FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (158))
                                               (Prims.of_int (8))
                                               (Prims.of_int (160))
                                               (Prims.of_int (11)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)
                  with
                  | FStar_Tactics_Result.Success (a1, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "experimental/FStar.InteractiveHelpers.Output.fst"
                                        (Prims.of_int (162))
                                        (Prims.of_int (2))
                                        (Prims.of_int (171))
                                        (Prims.of_int (33)))))
                       with
                       | true ->
                           (match match match (FStar_InteractiveHelpers_Base.term_construct
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
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (33))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (42))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                  (Prims.of_int (162))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (162))
                                                                  (Prims.of_int (42))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                                            (Prims.of_int (162))
                                                            (Prims.of_int (25))
                                                            (Prims.of_int (162))
                                                            (Prims.of_int (41))))))
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a2, ps'2) ->
                                            (match FStar_Tactics_Types.tracepoint
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
                                                       "qualifier: " a2),
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
                                              (e, ps'2)
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Output.fst"
                                                        (Prims.of_int (162))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (162))
                                                        (Prims.of_int (42)))))
                                       with
                                       | true ->
                                           (FStar_Tactics_Builtins.print a2)
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "experimental/FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (162))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (162))
                                                         (Prims.of_int (42)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)
                            with
                            | FStar_Tactics_Result.Success (a2, ps'2) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'2
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (163))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (171))
                                                  (Prims.of_int (33)))))
                                 with
                                 | true ->
                                     (match match (FStar_Tactics_Builtins.inspect
                                                     t)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (33))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (11))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                (Prims.of_int (163))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (163))
                                                                (Prims.of_int (23))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3, ps'3) ->
                                                (match FStar_Tactics_Types.tracepoint
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'3
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                  (Prims.of_int (163))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (169))
                                                                  (Prims.of_int (11)))))
                                                 with
                                                 | true ->
                                                     ((match a3 with
                                                       | FStar_Reflection_Data.Tv_Var
                                                           bv ->
                                                           (fun ps1 ->
                                                              match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (49)))))
                                                              with
                                                              | true ->
                                                                  (FStar_Tactics_Builtins.print
                                                                    (Prims.strcat
                                                                    "Tv_Var: ppname: "
                                                                    (Prims.strcat
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_ppname
                                                                    (Prims.strcat
                                                                    "; index: "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_index)
                                                                    (Prims.strcat
                                                                    "; sort: "
                                                                    (FStar_Reflection_Builtins.term_to_string
                                                                    (FStar_Reflection_Builtins.inspect_bv
                                                                    bv).FStar_Reflection_Data.bv_sort)))))))
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (49)))))))
                                                       | uu___ ->
                                                           (fun s ->
                                                              FStar_Tactics_Result.Success
                                                                ((), s))))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'3
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (163))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (169))
                                                                   (Prims.of_int (11)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e, ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3)
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3, ps'3) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'3
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                                            (Prims.of_int (171))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (171))
                                                            (Prims.of_int (33)))))
                                           with
                                           | true ->
                                               (FStar_Tactics_Builtins.print
                                                  "end of _debug_print_var")
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'3
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "experimental/FStar.InteractiveHelpers.Output.fst"
                                                             (Prims.of_int (171))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (171))
                                                             (Prims.of_int (33)))))))
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
let magic_witness : 'a . unit -> 'a =
  fun uu___ -> failwith "Not yet implemented:magic_witness"
let (tadmit_no_warning :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "InteractiveHelpers"; "Output"; "magic_witness"])))
let (pp_tac :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match match match (FStar_Tactics_Derived.cur_goal ())
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
                                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (185))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (185))
                                                              (Prims.of_int (62))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "experimental/FStar.InteractiveHelpers.Output.fst"
                                                        (Prims.of_int (185))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (185))
                                                        (Prims.of_int (62))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (185))
                                                  (Prims.of_int (31))
                                                  (Prims.of_int (185))
                                                  (Prims.of_int (61))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "experimental/FStar.InteractiveHelpers.Output.fst"
                                            (Prims.of_int (185))
                                            (Prims.of_int (47))
                                            (Prims.of_int (185))
                                            (Prims.of_int (60))))))
                        with
                        | FStar_Tactics_Result.Success (a, ps') ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "experimental/FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (185))
                                              (Prims.of_int (31))
                                              (Prims.of_int (185))
                                              (Prims.of_int (61)))))
                             with
                             | true ->
                                 FStar_Tactics_Result.Success
                                   ((FStar_Reflection_Builtins.term_to_string
                                       a),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "experimental/FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (185))
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (185))
                                                 (Prims.of_int (61))))))))
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
                             ((Prims.strcat "post-processing: " a),
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
                               (Prims.mk_range
                                  "experimental/FStar.InteractiveHelpers.Output.fst"
                                  (Prims.of_int (185)) (Prims.of_int (2))
                                  (Prims.of_int (185)) (Prims.of_int (62)))))
                 with
                 | true ->
                     (FStar_Tactics_Builtins.print a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "experimental/FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (185)) (Prims.of_int (2))
                                   (Prims.of_int (185)) (Prims.of_int (62)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "experimental/FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (186)) (Prims.of_int (2))
                            (Prims.of_int (187)) (Prims.of_int (9)))))
           with
           | true ->
               (match (FStar_Tactics_Builtins.dump "")
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "experimental/FStar.InteractiveHelpers.Output.fst"
                                          (Prims.of_int (186))
                                          (Prims.of_int (2))
                                          (Prims.of_int (187))
                                          (Prims.of_int (9))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "experimental/FStar.InteractiveHelpers.Output.fst"
                                    (Prims.of_int (186)) (Prims.of_int (2))
                                    (Prims.of_int (186)) (Prims.of_int (9))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "experimental/FStar.InteractiveHelpers.Output.fst"
                                      (Prims.of_int (187)) (Prims.of_int (2))
                                      (Prims.of_int (187)) (Prims.of_int (9)))))
                     with
                     | true ->
                         (FStar_Tactics_Derived.trefl ())
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "experimental/FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (187))
                                       (Prims.of_int (2))
                                       (Prims.of_int (187))
                                       (Prims.of_int (9)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')