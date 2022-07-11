open Prims

let rec first :
  'a 'b .
    ('a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Tactics_Derived.fail "no cands"
      | x::xs ->
          FStar_Tactics_Derived.or_else (fun uu___ -> f x)
            (fun uu___ -> first f xs)
let rec (tcresolve' :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun seen ->
    fun fuel ->
      fun ps ->
        match (if fuel <= Prims.int_zero
               then FStar_Tactics_Derived.fail "out of fuel"
               else (fun s -> FStar_Tactics_Result.Success ((), s)))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (36)) (Prims.of_int (4))
                            (Prims.of_int (37)) (Prims.of_int (26))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (38)) (Prims.of_int (4))
                              (Prims.of_int (43)) (Prims.of_int (137)))))
             with
             | true ->
                 (match (FStar_Tactics_Derived.debug
                           (Prims.strcat "fuel = " (Prims.string_of_int fuel)))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (38))
                                            (Prims.of_int (4))
                                            (Prims.of_int (43))
                                            (Prims.of_int (137))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (38)) (Prims.of_int (4))
                                      (Prims.of_int (38)) (Prims.of_int (42))))))
                  with
                  | FStar_Tactics_Result.Success (a1, ps'1) ->
                      (match FStar_Tactics_Types.tracepoint
                               (FStar_Tactics_Types.set_proofstate_range ps'1
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (39))
                                        (Prims.of_int (4))
                                        (Prims.of_int (43))
                                        (Prims.of_int (137)))))
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
                                                      "FStar.Tactics.Typeclasses.fst"
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (137))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (39))
                                                (Prims.of_int (12))
                                                (Prims.of_int (39))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'2) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'2
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (40))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (43))
                                                  (Prims.of_int (137)))))
                                 with
                                 | true ->
                                     (match (if
                                               FStar_List_Tot_Base.existsb
                                                 (FStar_Reflection_Builtins.term_eq
                                                    a2) seen
                                             then
                                               FStar_Tactics_Derived.fail
                                                 "loop"
                                             else
                                               (fun s ->
                                                  FStar_Tactics_Result.Success
                                                    ((), s)))
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Typeclasses.fst"
                                                                (Prims.of_int (40))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (137))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Typeclasses.fst"
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (41))
                                                          (Prims.of_int (17))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3, ps'3) ->
                                          (match FStar_Tactics_Types.tracepoint
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'3
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Typeclasses.fst"
                                                            (Prims.of_int (42))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (43))
                                                            (Prims.of_int (137)))))
                                           with
                                           | true ->
                                               (match FStar_Tactics_Types.tracepoint
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (137))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Typeclasses.fst"
                                                                 (Prims.of_int (43))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (43))
                                                                 (Prims.of_int (137)))))
                                                with
                                                | true ->
                                                    (FStar_Tactics_Derived.or_else
                                                       (local (a2 :: seen)
                                                          fuel)
                                                       (fun uu___ ->
                                                          FStar_Tactics_Derived.or_else
                                                            (global (a2 ::
                                                               seen) fuel)
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Derived.fail
                                                                 (Prims.strcat
                                                                    "could not solve constraint: "
                                                                    (
                                                                    FStar_Reflection_Builtins.term_to_string
                                                                    a2)))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (137))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (43))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (43))
                                                                  (Prims.of_int (137))))))))
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
and (local :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      unit ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun seen ->
    fun fuel ->
      fun uu___ ->
        fun ps ->
          match match (FStar_Tactics_Derived.cur_env ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (45))
                                          (Prims.of_int (13))
                                          (Prims.of_int (45))
                                          (Prims.of_int (40))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (45)) (Prims.of_int (28))
                                    (Prims.of_int (45)) (Prims.of_int (40))))))
                with
                | FStar_Tactics_Result.Success (a, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (45)) (Prims.of_int (13))
                                      (Prims.of_int (45)) (Prims.of_int (40)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           ((FStar_Reflection_Builtins.binders_of_env a),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (45))
                                         (Prims.of_int (13))
                                         (Prims.of_int (45))
                                         (Prims.of_int (40))))))))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (46)) (Prims.of_int (4))
                                (Prims.of_int (46)) (Prims.of_int (74)))))
               with
               | true ->
                   (first
                      (fun b ->
                         fun ps1 ->
                           match (FStar_Tactics_Builtins.pack
                                    (FStar_Reflection_Data.Tv_Var
                                       (FStar_Reflection_Derived.bv_of_binder
                                          b)))
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (46))
                                               (Prims.of_int (38))
                                               (Prims.of_int (46))
                                               (Prims.of_int (70))))))
                           with
                           | FStar_Tactics_Result.Success (a1, ps'1) ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (46))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (46))
                                                 (Prims.of_int (70)))))
                                with
                                | true ->
                                    (trywith seen fuel a1)
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (70)))))))
                           | FStar_Tactics_Result.Failed (e, ps'1) ->
                               FStar_Tactics_Result.Failed (e, ps'1)) a)
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (46)) (Prims.of_int (4))
                                 (Prims.of_int (46)) (Prims.of_int (74)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
and (global :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      unit ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun seen ->
    fun fuel ->
      fun uu___ ->
        fun ps ->
          match match (FStar_Tactics_Derived.cur_env ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (48))
                                          (Prims.of_int (16))
                                          (Prims.of_int (48))
                                          (Prims.of_int (54))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (48)) (Prims.of_int (42))
                                    (Prims.of_int (48)) (Prims.of_int (54))))))
                with
                | FStar_Tactics_Result.Success (a, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (48)) (Prims.of_int (16))
                                      (Prims.of_int (48)) (Prims.of_int (54)))))
                     with
                     | true ->
                         FStar_Tactics_Result.Success
                           ((FStar_Reflection_Builtins.lookup_attr
                               (FStar_Reflection_Builtins.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Typeclasses";
                                        "tcinstance"]))) a),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (48))
                                         (Prims.of_int (16))
                                         (Prims.of_int (48))
                                         (Prims.of_int (54))))))))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (49)) (Prims.of_int (4))
                                (Prims.of_int (49)) (Prims.of_int (65)))))
               with
               | true ->
                   (first
                      (fun fv ->
                         fun ps1 ->
                           match (FStar_Tactics_Builtins.pack
                                    (FStar_Reflection_Data.Tv_FVar fv))
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (49))
                                               (Prims.of_int (39))
                                               (Prims.of_int (49))
                                               (Prims.of_int (58))))))
                           with
                           | FStar_Tactics_Result.Success (a1, ps'1) ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (49))
                                                 (Prims.of_int (21))
                                                 (Prims.of_int (49))
                                                 (Prims.of_int (58)))))
                                with
                                | true ->
                                    (trywith seen fuel a1)
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (58)))))))
                           | FStar_Tactics_Result.Failed (e, ps'1) ->
                               FStar_Tactics_Result.Failed (e, ps'1)) a)
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (49)) (Prims.of_int (4))
                                 (Prims.of_int (49)) (Prims.of_int (65)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
and (trywith :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      FStar_Reflection_Types.term ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun seen ->
    fun fuel ->
      fun t ->
        fun ps ->
          match (FStar_Tactics_Derived.debug
                   (Prims.strcat "Trying to apply hypothesis/instance: "
                      (FStar_Reflection_Builtins.term_to_string t)))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (51)) (Prims.of_int (4))
                              (Prims.of_int (51)) (Prims.of_int (70))))))
          with
          | FStar_Tactics_Result.Success (a, ps') ->
              (match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (52)) (Prims.of_int (4))
                                (Prims.of_int (52)) (Prims.of_int (73)))))
               with
               | true ->
                   (FStar_Tactics_Derived.seq
                      (fun uu___ -> FStar_Tactics_Derived.apply_noinst t)
                      (fun uu___ -> tcresolve' seen (fuel - Prims.int_one)))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (52)) (Prims.of_int (4))
                                 (Prims.of_int (52)) (Prims.of_int (73)))))))
          | FStar_Tactics_Result.Failed (e, ps') ->
              FStar_Tactics_Result.Failed (e, ps')
let rec (maybe_intros :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (55)) (Prims.of_int (10))
                          (Prims.of_int (55)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (56)) (Prims.of_int (2))
                            (Prims.of_int (60)) (Prims.of_int (11)))))
           with
           | true ->
               ((match FStar_Reflection_Builtins.inspect_ln a with
                 | FStar_Reflection_Data.Tv_Arrow (uu___1, uu___2) ->
                     (fun ps1 ->
                        match match (FStar_Tactics_Builtins.intro ())
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Typeclasses.fst"
                                                        (Prims.of_int (58))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (58))
                                                        (Prims.of_int (21))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (21))))))
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Typeclasses.fst"
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (21)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (58))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (58))
                                                       (Prims.of_int (21))))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a1, ps'1) ->
                            (match FStar_Tactics_Types.tracepoint
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Typeclasses.fst"
                                              (Prims.of_int (59))
                                              (Prims.of_int (4))
                                              (Prims.of_int (59))
                                              (Prims.of_int (19)))))
                             with
                             | true ->
                                 (maybe_intros ())
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (59))
                                               (Prims.of_int (4))
                                               (Prims.of_int (59))
                                               (Prims.of_int (19)))))))
                        | FStar_Tactics_Result.Failed (e, ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu___1 -> (fun s -> FStar_Tactics_Result.Success ((), s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (56)) (Prims.of_int (2))
                             (Prims.of_int (60)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (tcresolve :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (maybe_intros ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (67)) (Prims.of_int (4))
                          (Prims.of_int (67)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (68)) (Prims.of_int (4))
                            (Prims.of_int (71)) (Prims.of_int (18)))))
           with
           | true ->
               (FStar_Tactics_Derived.try_with
                  (fun uu___1 ->
                     match () with | () -> tcresolve' [] (Prims.of_int (16)))
                  (fun uu___1 ->
                     match uu___1 with
                     | FStar_Tactics_Common.TacticFailure s ->
                         FStar_Tactics_Derived.fail
                           (Prims.strcat "Typeclass resolution failed: " s)
                     | e -> FStar_Tactics_Effect.raise e))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (68)) (Prims.of_int (4))
                             (Prims.of_int (71)) (Prims.of_int (18)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 tcresolve)
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)
let solve : 'a . 'a -> 'a = fun ev -> ev
let rec (mk_abs :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_Types.proofstate ->
        FStar_Reflection_Types.term FStar_Tactics_Result.__result)
  =
  fun bs ->
    fun body ->
      match bs with
      | [] -> (fun s -> FStar_Tactics_Result.Success (body, s))
      | b::bs1 ->
          (fun ps ->
             match match (mk_abs bs1 body)
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (82))
                                             (Prims.of_int (20))
                                             (Prims.of_int (82))
                                             (Prims.of_int (47))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Typeclasses.fst"
                                       (Prims.of_int (82))
                                       (Prims.of_int (30))
                                       (Prims.of_int (82))
                                       (Prims.of_int (46))))))
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (82))
                                         (Prims.of_int (20))
                                         (Prims.of_int (82))
                                         (Prims.of_int (47)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Data.Tv_Abs (b, a)),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (82))
                                            (Prims.of_int (20))
                                            (Prims.of_int (82))
                                            (Prims.of_int (47))))))))
                   | FStar_Tactics_Result.Failed (e, ps') ->
                       FStar_Tactics_Result.Failed (e, ps')
             with
             | FStar_Tactics_Result.Success (a, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.Typeclasses.fst"
                                   (Prims.of_int (82)) (Prims.of_int (15))
                                   (Prims.of_int (82)) (Prims.of_int (47)))))
                  with
                  | true ->
                      (FStar_Tactics_Builtins.pack a)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (82)) (Prims.of_int (15))
                                    (Prims.of_int (82)) (Prims.of_int (47)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec last :
  'a .
    'a Prims.list ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun l ->
    match l with
    | [] -> FStar_Tactics_Derived.fail "last: empty list"
    | x::[] -> (fun s -> FStar_Tactics_Result.Success (x, s))
    | uu___::xs -> last xs
let (mk_class :
  Prims.string ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Data.decls FStar_Tactics_Result.__result)
  =
  fun nm ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (92)) (Prims.of_int (13))
                             (Prims.of_int (92)) (Prims.of_int (26))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (93)) (Prims.of_int (4))
                       (Prims.of_int (172)) (Prims.of_int (8)))))
      with
      | true ->
          (match match (FStar_Tactics_Builtins.top_env ())
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
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (92))
                                                       (Prims.of_int (13))
                                                       (Prims.of_int (92))
                                                       (Prims.of_int (26))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (93))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (172))
                                                 (Prims.of_int (8))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (93))
                                           (Prims.of_int (12))
                                           (Prims.of_int (93))
                                           (Prims.of_int (38))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (93)) (Prims.of_int (23))
                                     (Prims.of_int (93)) (Prims.of_int (35))))))
                 with
                 | FStar_Tactics_Result.Success (a, ps') ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Typeclasses.fst"
                                       (Prims.of_int (93))
                                       (Prims.of_int (12))
                                       (Prims.of_int (93))
                                       (Prims.of_int (38)))))
                      with
                      | true ->
                          FStar_Tactics_Result.Success
                            ((FStar_Reflection_Builtins.lookup_typ a
                                (FStar_Reflection_Builtins.explode_qn nm)),
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (93))
                                          (Prims.of_int (12))
                                          (Prims.of_int (93))
                                          (Prims.of_int (38))))))))
                 | FStar_Tactics_Result.Failed (e, ps') ->
                     FStar_Tactics_Result.Failed (e, ps')
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (94)) (Prims.of_int (4))
                                 (Prims.of_int (172)) (Prims.of_int (8)))))
                with
                | true ->
                    (match (FStar_Tactics_Derived.guard
                              (FStar_Pervasives_Native.uu___is_Some a))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (94))
                                               (Prims.of_int (4))
                                               (Prims.of_int (172))
                                               (Prims.of_int (8))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (94))
                                         (Prims.of_int (4))
                                         (Prims.of_int (94))
                                         (Prims.of_int (19))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (95))
                                           (Prims.of_int (4))
                                           (Prims.of_int (172))
                                           (Prims.of_int (8)))))
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
                                                            "FStar.Tactics.Typeclasses.fst"
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (172))
                                                            (Prims.of_int (8))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Typeclasses.fst"
                                                      (Prims.of_int (95))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (95))
                                                      (Prims.of_int (19))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (95))
                                                (Prims.of_int (4))
                                                (Prims.of_int (172))
                                                (Prims.of_int (8)))))
                               with
                               | true ->
                                   ((match a with
                                     | FStar_Pervasives_Native.Some se ->
                                         (fun ps1 ->
                                            match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps1
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (96))
                                                                   (Prims.of_int (23))
                                                                   (Prims.of_int (96))
                                                                   (Prims.of_int (122))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (97))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (172))
                                                             (Prims.of_int (8)))))
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
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (122))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (30))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (98))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (172))
                                                                  (Prims.of_int (8)))))
                                                 with
                                                 | true ->
                                                     (match (FStar_Tactics_Derived.guard
                                                               (FStar_Reflection_Data.uu___is_Sg_Inductive
                                                                  (FStar_Reflection_Builtins.inspect_sigelt
                                                                    se)))
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (122))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (28))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a2, ps'2) ->
                                                          (match FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
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
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                with
                                                                | true ->
                                                                    ((match 
                                                                    FStar_Reflection_Builtins.inspect_sigelt
                                                                    se
                                                                    with
                                                                    | FStar_Reflection_Data.Sg_Inductive
                                                                    (name,
                                                                    us,
                                                                    params,
                                                                    ty,
                                                                    ctors) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (last
                                                                    name)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (29))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    ctors) =
                                                                    Prims.int_one))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (42))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match ctors
                                                                    with
                                                                    | (c_name,
                                                                    ty1)::[]
                                                                    ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                    ty1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (107))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a5
                                                                    with
                                                                    | (bs,
                                                                    cod) ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Reflection_Data.uu___is_C_Total
                                                                    (FStar_Reflection_Builtins.inspect_comp
                                                                    cod)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (22))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match 
                                                                    FStar_Reflection_Builtins.inspect_comp
                                                                    cod
                                                                    with
                                                                    | FStar_Reflection_Data.C_Total
                                                                    (cod1,
                                                                    uu___) ->
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b ->
                                                                    fun ps6
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (40))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
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
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.fresh_bv_named
                                                                    "d" cod1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (50))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ())
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
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (60))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (47))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (60)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    a9
                                                                    [
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "__proj__Mk"
                                                                    (Prims.strcat
                                                                    a3
                                                                    "__item__"))
                                                                    (FStar_Reflection_Derived.name_of_binder
                                                                    b)]),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (60))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    a9)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (63))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,
                                                                    ps'10) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.top_env
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (59))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (49))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,
                                                                    ps'11) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (59)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.lookup_typ
                                                                    a11 a9),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (59))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,
                                                                    ps'11) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (62)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a11
                                                                    with
                                                                    | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "mk_class: proj not found?"
                                                                    | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_sigelt
                                                                    se1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Sg_Let
                                                                    (uu___1,
                                                                    lbs) ->
                                                                    (fun ps7
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_SyntaxHelpers.lookup_lb_view
                                                                    lbs a9)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (54))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,
                                                                    ps'12) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (61)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a12
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_Data.lb_fv
                                                                    = uu___2;
                                                                    FStar_Reflection_Data.lb_us
                                                                    = uu___3;
                                                                    FStar_Reflection_Data.lb_typ
                                                                    = typ;
                                                                    FStar_Reflection_Data.lb_def
                                                                    = uu___4;_}
                                                                    -> typ)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (61))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12))
                                                                    | 
                                                                    uu___1 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "mk_class: proj not Sg_Let?")))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (62)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,
                                                                    ps'11) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                    a11)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (56))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,
                                                                    ps'12) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a12
                                                                    with
                                                                    | (bs1,
                                                                    cod2) ->
                                                                    (fun ps7
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (87))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match 
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1
                                                                    with
                                                                    | (ps8,
                                                                    bs2) ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "mk_class: impossible, no binders"
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    (fun ps9
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match 
                                                                    FStar_Reflection_Builtins.inspect_binder
                                                                    b1
                                                                    with
                                                                    | (bv,
                                                                    aq) ->
                                                                    (fun ps10
                                                                    ->
                                                                    match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_SyntaxHelpers.mk_arr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ps8
                                                                    ((FStar_Reflection_Builtins.pack_binder
                                                                    bv
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))
                                                                    []) ::
                                                                    bs'))
                                                                    cod2)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49))))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (87))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (49)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,
                                                                    ps'12) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b1
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.binder_set_qual
                                                                    FStar_Reflection_Data.Q_Implicit
                                                                    b1), s))
                                                                    params)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (81))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,
                                                                    ps'13) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (46)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    a13
                                                                    [
                                                                    FStar_Reflection_Builtins.pack_binder
                                                                    a8
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))
                                                                    []]),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (46))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,
                                                                    ps'13) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    (FStar_Reflection_Builtins.pack_binder
                                                                    a8
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))
                                                                    []))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (67))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,
                                                                    ps'14) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (68)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a14],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (68))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,
                                                                    ps'14) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.mk_e_app
                                                                    a10 a14),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,
                                                                    ps'14) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (mk_abs
                                                                    a13 a14)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (69)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,
                                                                    ps'13) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match 
                                                                    FStar_Reflection_Builtins.inspect_binder
                                                                    b
                                                                    with
                                                                    | 
                                                                    (uu___1,
                                                                    (uu___2,
                                                                    attrs))
                                                                    ->
                                                                    FStar_Reflection_Builtins.set_sigelt_attrs
                                                                    attrs
                                                                    (FStar_Reflection_Builtins.set_sigelt_quals
                                                                    (FStar_List_Tot_Base.filter
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Inline_for_extraction
                                                                    -> true
                                                                    | 
                                                                    FStar_Reflection_Data.NoExtract
                                                                    -> true
                                                                    | 
                                                                    uu___4 ->
                                                                    false)
                                                                    (FStar_Reflection_Builtins.sigelt_quals
                                                                    se))
                                                                    (FStar_Reflection_Builtins.pack_sigelt
                                                                    (FStar_Reflection_Data.Sg_Let
                                                                    (false,
                                                                    [
                                                                    FStar_Reflection_Builtins.pack_lb
                                                                    {
                                                                    FStar_Reflection_Data.lb_fv
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    (FStar_List_Tot_Base.op_At
                                                                    a7
                                                                    [
                                                                    FStar_Reflection_Derived.name_of_binder
                                                                    b]));
                                                                    FStar_Reflection_Data.lb_us
                                                                    = us;
                                                                    FStar_Reflection_Data.lb_typ
                                                                    = a12;
                                                                    FStar_Reflection_Data.lb_def
                                                                    = a13
                                                                    }])))))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (20))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12)))
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
                                                                    ps'10)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    bs)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))))
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
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (8))))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e, ps'2) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'2))))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (95))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (172))
                                                             (Prims.of_int (8))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (95))
                                                       (Prims.of_int (18))
                                                       (Prims.of_int (95))
                                                       (Prims.of_int (19))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (95))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (172))
                                                 (Prims.of_int (8))))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.mk_class"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 mk_class)
             FStar_Syntax_Embeddings.e_string
             (FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt) psc ncb args)