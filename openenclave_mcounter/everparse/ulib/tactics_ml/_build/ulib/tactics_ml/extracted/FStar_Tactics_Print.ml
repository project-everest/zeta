open Prims
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
let rec print_list_aux :
  'a .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         Prims.string FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result
  =
  fun f ->
    fun xs ->
      match xs with
      | [] -> (fun s -> FStar_Tactics_Result.Success ("", s))
      | x::[] -> f x
      | x::xs1 ->
          (fun ps ->
             match (f x)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (16)) (Prims.of_int (13))
                                 (Prims.of_int (16)) (Prims.of_int (16))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Print.fst"
                                   (Prims.of_int (16)) (Prims.of_int (13))
                                   (Prims.of_int (16)) (Prims.of_int (45)))))
                  with
                  | true ->
                      (match match (print_list_aux f xs1)
                                     (FStar_Tactics_Types.incr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Print.fst"
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (45))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (45))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (26))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (45))))))
                             with
                             | FStar_Tactics_Result.Success (a2, ps'1) ->
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
                                        ((Prims.strcat "; " a2),
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
                       | FStar_Tactics_Result.Success (a2, ps'1) ->
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
                                  ((Prims.strcat a1 a2),
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
                 FStar_Tactics_Result.Failed (e, ps'))
let print_list :
  'a .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         Prims.string FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          Prims.string FStar_Tactics_Result.__result
  =
  fun f ->
    fun l ->
      fun ps ->
        match match (print_list_aux f l)
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.Print.fst"
                                        (Prims.of_int (20))
                                        (Prims.of_int (9))
                                        (Prims.of_int (20))
                                        (Prims.of_int (33))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Print.fst"
                                  (Prims.of_int (20)) (Prims.of_int (9))
                                  (Prims.of_int (20)) (Prims.of_int (27))))))
              with
              | FStar_Tactics_Result.Success (a1, ps') ->
                  (match FStar_Tactics_Types.tracepoint
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31)))))
                   with
                   | true ->
                       FStar_Tactics_Result.Success
                         ((Prims.strcat a1 "]"),
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (603))
                                       (Prims.of_int (19))
                                       (Prims.of_int (603))
                                       (Prims.of_int (31))))))))
              | FStar_Tactics_Result.Failed (e, ps') ->
                  FStar_Tactics_Result.Failed (e, ps')
        with
        | FStar_Tactics_Result.Success (a1, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (20)) (Prims.of_int (3))
                              (Prims.of_int (20)) (Prims.of_int (33)))))
             with
             | true ->
                 FStar_Tactics_Result.Success
                   ((Prims.strcat "[" a1),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (20)) (Prims.of_int (3))
                                 (Prims.of_int (20)) (Prims.of_int (33))))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')
let rec (term_to_ast_string :
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
                       (Prims.mk_range "FStar.Tactics.Print.fst"
                          (Prims.of_int (23)) (Prims.of_int (8))
                          (Prims.of_int (23)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Print.fst"
                            (Prims.of_int (23)) (Prims.of_int (2))
                            (Prims.of_int (56)) (Prims.of_int (21)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Data.Tv_Var bv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((Prims.strcat "Tv_Var "
                              (FStar_Reflection_Derived.bv_to_string bv)), s))
                 | FStar_Reflection_Data.Tv_BVar bv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((Prims.strcat "Tv_BVar "
                              (FStar_Reflection_Derived.bv_to_string bv)), s))
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((Prims.strcat "Tv_FVar "
                              (FStar_Reflection_Derived.fv_to_string fv)), s))
                 | FStar_Reflection_Data.Tv_App (hd, (a1, uu___)) ->
                     (fun ps1 ->
                        match match match (term_to_ast_string hd)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (95))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (42))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (95))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (43))
                                                        (Prims.of_int (27))
                                                        (Prims.of_int (64))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Print.fst"
                                                          (Prims.of_int (27))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (27))
                                                          (Prims.of_int (95)))))
                                         with
                                         | true ->
                                             (match match (term_to_ast_string
                                                             a1)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (95))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (94))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (94))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a3, ps'2) ->
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
                                                                   ", " a3),
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
                                                  (a3, ps'2) ->
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
                                                         ((Prims.strcat a2 a3),
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
                                        FStar_Tactics_Result.Failed (e, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a2, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (27))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (27))
                                                    (Prims.of_int (95)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a2),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (27))
                                                       (Prims.of_int (36))
                                                       (Prims.of_int (27))
                                                       (Prims.of_int (95))))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
                        with
                        | FStar_Tactics_Result.Success (a2, ps'1) ->
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
                                   ((Prims.strcat "Tv_App " a2),
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
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | FStar_Reflection_Data.Tv_Abs (x, e) ->
                     (fun ps1 ->
                        match match match match (term_to_ast_string e)
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (86))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (86))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (85))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (28))
                                                              (Prims.of_int (65))
                                                              (Prims.of_int (28))
                                                              (Prims.of_int (85))))))
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
                                                     ((Prims.strcat ", " a1),
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
                                              (e1, ps'1) ->
                                              FStar_Tactics_Result.Failed
                                                (e1, ps'1)
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
                                               ((Prims.strcat
                                                   (FStar_Reflection_Derived.binder_to_string
                                                      x) a1),
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
                                    | FStar_Tactics_Result.Failed (e1, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed
                                          (e1, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (30))
                                                    (Prims.of_int (28))
                                                    (Prims.of_int (86)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (28))
                                                       (Prims.of_int (30))
                                                       (Prims.of_int (28))
                                                       (Prims.of_int (86))))))))
                              | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                  FStar_Tactics_Result.Failed (e1, ps'1)
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
                                   ((Prims.strcat "Tv_Abs " a1),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (31))))))))
                        | FStar_Tactics_Result.Failed (e1, ps'1) ->
                            FStar_Tactics_Result.Failed (e1, ps'1))
                 | FStar_Reflection_Data.Tv_Arrow (x, c) ->
                     (fun ps1 ->
                        match match match match (comp_to_ast_string c)
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (90))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (90))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (89))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (69))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (89))))))
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
                                                     ((Prims.strcat ", " a1),
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
                                                          "prims.fst"
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (31)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((Prims.strcat
                                                   (FStar_Reflection_Derived.binder_to_string
                                                      x) a1),
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
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (34))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (90)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (29))
                                                       (Prims.of_int (34))
                                                       (Prims.of_int (29))
                                                       (Prims.of_int (90))))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
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
                                   ((Prims.strcat "Tv_Arrow " a1),
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
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | FStar_Reflection_Data.Tv_Type uu___ ->
                     (fun s -> FStar_Tactics_Result.Success ("Type", s))
                 | FStar_Reflection_Data.Tv_Refine (x, e) ->
                     (fun ps1 ->
                        match match match match (term_to_ast_string e)
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (88))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (88))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (87))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (31))
                                                              (Prims.of_int (67))
                                                              (Prims.of_int (31))
                                                              (Prims.of_int (87))))))
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
                                                     ((Prims.strcat ", " a1),
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
                                              (e1, ps'1) ->
                                              FStar_Tactics_Result.Failed
                                                (e1, ps'1)
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
                                               ((Prims.strcat
                                                   (FStar_Reflection_Derived.bv_to_string
                                                      x) a1),
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
                                    | FStar_Tactics_Result.Failed (e1, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed
                                          (e1, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (88)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (36))
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (88))))))))
                              | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                  FStar_Tactics_Result.Failed (e1, ps'1)
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
                                   ((Prims.strcat "Tv_Refine " a1),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (31))))))))
                        | FStar_Tactics_Result.Failed (e1, ps'1) ->
                            FStar_Tactics_Result.Failed (e1, ps'1))
                 | FStar_Reflection_Data.Tv_Const c -> const_to_ast_string c
                 | FStar_Reflection_Data.Tv_Uvar (i, uu___) ->
                     (fun s ->
                        FStar_Tactics_Result.Success
                          ((Prims.strcat "Tv_Uvar " (Prims.string_of_int i)),
                            s))
                 | FStar_Reflection_Data.Tv_Let (recf, uu___, x, e1, e2) ->
                     (fun ps1 ->
                        match match match match match match match (term_to_ast_string
                                                                    e1)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
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
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (51))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a1, ps'1) ->
                                                                (match 
                                                                   FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51)))))
                                                                 with
                                                                 | true ->
                                                                    (match 
                                                                    match 
                                                                    (term_to_ast_string
                                                                    e2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (51))))))
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
                                                                    ", " a2),
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
                                                                    a1 a2),
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
                                                                    (e, ps'2)))
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
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31)))))
                                                           with
                                                           | true ->
                                                               FStar_Tactics_Result.Success
                                                                 ((Prims.strcat
                                                                    ", " a1),
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
                                                               (FStar_Reflection_Derived.bv_to_string
                                                                  x) a1),
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
                                                     ((Prims.strcat ", " a1),
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
                                                          "prims.fst"
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (603))
                                                          (Prims.of_int (31)))))
                                         with
                                         | true ->
                                             FStar_Tactics_Result.Success
                                               ((Prims.strcat
                                                   (Prims.string_of_bool recf)
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
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (38))
                                                    (Prims.of_int (52)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (35))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (38))
                                                       (Prims.of_int (52))))))))
                              | FStar_Tactics_Result.Failed (e, ps'1) ->
                                  FStar_Tactics_Result.Failed (e, ps'1)
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
                                   ((Prims.strcat "Tv_Let " a1),
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
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | FStar_Reflection_Data.Tv_Match (e, ret_opt, brs) ->
                     (fun ps1 ->
                        match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (41))
                                               (Prims.of_int (6))
                                               (Prims.of_int (43))
                                               (Prims.of_int (53))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Print.fst"
                                         (Prims.of_int (44))
                                         (Prims.of_int (4))
                                         (Prims.of_int (53))
                                         (Prims.of_int (35)))))
                        with
                        | true ->
                            (match match match (term_to_ast_string e)
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
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (53))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (35))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (35))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Print.fst"
                                                                   (Prims.of_int (45))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (53))
                                                                   (Prims.of_int (35))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Print.fst"
                                                             (Prims.of_int (46))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (46))
                                                             (Prims.of_int (28))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a1, ps'1) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Print.fst"
                                                               (Prims.of_int (45))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (53))
                                                               (Prims.of_int (35)))))
                                              with
                                              | true ->
                                                  (match match match 
                                                                 (match ret_opt
                                                                  with
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ("None",
                                                                    s))
                                                                  | FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inl
                                                                    t1,
                                                                    tacopt)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (term_to_ast_string
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (57))))))
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (85)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (match tacopt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ("", s))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tac ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (term_to_ast_string
                                                                    tac)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (53))))))
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
                                                                    " by " a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (85))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (85))))))
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
                                                                    a2 a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2))
                                                                  | FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inr
                                                                    c,
                                                                    tacopt)
                                                                    ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (comp_to_ast_string
                                                                    c)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (57))))))
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (85)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (match tacopt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun s ->
                                                                    FStar_Tactics_Result.Success
                                                                    ("", s))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tac ->
                                                                    (fun ps3
                                                                    ->
                                                                    match 
                                                                    (term_to_ast_string
                                                                    tac)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (53))))))
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
                                                                    " by " a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (85))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (85))))))
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
                                                                    a2 a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)))
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (86))))))
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
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    match 
                                                                    (branches_to_ast_string
                                                                    brs)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (53))
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
                                                                    ", " a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)
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
                                                                    a2 a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (603))
                                                                    (Prims.of_int (31))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3) ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'3)))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e1, ps'2)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e1,
                                                                    ps'2)
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
                                                                    ", " a2),
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
                                                             (e1, ps'2) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e1, ps'2)
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
                                                                  a1 a2),
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
                                                       (e1, ps'2) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e1, ps'2)))
                                         | FStar_Tactics_Result.Failed
                                             (e1, ps'1) ->
                                             FStar_Tactics_Result.Failed
                                               (e1, ps'1)
                                   with
                                   | FStar_Tactics_Result.Success (a1, ps'1)
                                       ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Print.fst"
                                                         (Prims.of_int (45))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (35)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((paren a1),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Print.fst"
                                                            (Prims.of_int (45))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (53))
                                                            (Prims.of_int (35))))))))
                                   | FStar_Tactics_Result.Failed (e1, ps'1)
                                       ->
                                       FStar_Tactics_Result.Failed (e1, ps'1)
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
                                        ((Prims.strcat "Tv_Match " a1),
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
                             | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                 FStar_Tactics_Result.Failed (e1, ps'1)))
                 | FStar_Reflection_Data.Tv_AscribedT (e, t1, uu___) ->
                     (fun ps1 ->
                        match match match (term_to_ast_string e)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (54))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (54))
                                                              (Prims.of_int (102))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (54))
                                                        (Prims.of_int (51))
                                                        (Prims.of_int (54))
                                                        (Prims.of_int (71))))))
                                    with
                                    | FStar_Tactics_Result.Success (a1, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Print.fst"
                                                          (Prims.of_int (54))
                                                          (Prims.of_int (50))
                                                          (Prims.of_int (54))
                                                          (Prims.of_int (102)))))
                                         with
                                         | true ->
                                             (match match (term_to_ast_string
                                                             t1)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (101))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (101))))))
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
                                                                   ", " a2),
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
                                                        (e1, ps'2) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e1, ps'2)
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
                                                         ((Prims.strcat a1 a2),
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
                                                  (e1, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e1, ps'2)))
                                    | FStar_Tactics_Result.Failed (e1, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed
                                          (e1, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (44))
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (102)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (102))))))))
                              | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                  FStar_Tactics_Result.Failed (e1, ps'1)
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
                                   ((Prims.strcat "Tv_AscribedT " a1),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (31))))))))
                        | FStar_Tactics_Result.Failed (e1, ps'1) ->
                            FStar_Tactics_Result.Failed (e1, ps'1))
                 | FStar_Reflection_Data.Tv_AscribedC (e, c, uu___) ->
                     (fun ps1 ->
                        match match match (term_to_ast_string e)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (102))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (55))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (55))
                                                              (Prims.of_int (102))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (55))
                                                        (Prims.of_int (51))
                                                        (Prims.of_int (55))
                                                        (Prims.of_int (71))))))
                                    with
                                    | FStar_Tactics_Result.Success (a1, ps'1)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Print.fst"
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (50))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (102)))))
                                         with
                                         | true ->
                                             (match match (comp_to_ast_string
                                                             c)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (101))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (101))))))
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
                                                                   ", " a2),
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
                                                        (e1, ps'2) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e1, ps'2)
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
                                                         ((Prims.strcat a1 a2),
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
                                                  (e1, ps'2) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e1, ps'2)))
                                    | FStar_Tactics_Result.Failed (e1, ps'1)
                                        ->
                                        FStar_Tactics_Result.Failed
                                          (e1, ps'1)
                              with
                              | FStar_Tactics_Result.Success (a1, ps'1) ->
                                  (match FStar_Tactics_Types.tracepoint
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (55))
                                                    (Prims.of_int (44))
                                                    (Prims.of_int (55))
                                                    (Prims.of_int (102)))))
                                   with
                                   | true ->
                                       FStar_Tactics_Result.Success
                                         ((paren a1),
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'1
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (55))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (55))
                                                       (Prims.of_int (102))))))))
                              | FStar_Tactics_Result.Failed (e1, ps'1) ->
                                  FStar_Tactics_Result.Failed (e1, ps'1)
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
                                   ((Prims.strcat "Tv_AscribedC " a1),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (31))))))))
                        | FStar_Tactics_Result.Failed (e1, ps'1) ->
                            FStar_Tactics_Result.Failed (e1, ps'1))
                 | FStar_Reflection_Data.Tv_Unknown ->
                     (fun s -> FStar_Tactics_Result.Success ("_", s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Print.fst"
                             (Prims.of_int (23)) (Prims.of_int (2))
                             (Prims.of_int (56)) (Prims.of_int (21)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
and (branches_to_ast_string :
  FStar_Reflection_Data.branch Prims.list ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  = fun brs -> print_list branch_to_ast_string brs
and (branch_to_ast_string :
  FStar_Reflection_Data.branch ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun b ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Print.fst"
                             (Prims.of_int (62)) (Prims.of_int (13))
                             (Prims.of_int (62)) (Prims.of_int (14))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.Print.fst"
                       (Prims.of_int (62)) (Prims.of_int (2))
                       (Prims.of_int (63)) (Prims.of_int (41)))))
      with
      | true ->
          ((match b with
            | (p, e) ->
                (fun ps1 ->
                   match match (term_to_ast_string e)
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps1
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Print.fst"
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (41))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Print.fst"
                                             (Prims.of_int (63))
                                             (Prims.of_int (20))
                                             (Prims.of_int (63))
                                             (Prims.of_int (40))))))
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
                                    ((Prims.strcat "_pat, " a),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range "prims.fst"
                                                  (Prims.of_int (603))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (603))
                                                  (Prims.of_int (31))))))))
                         | FStar_Tactics_Result.Failed (e1, ps') ->
                             FStar_Tactics_Result.Failed (e1, ps')
                   with
                   | FStar_Tactics_Result.Success (a, ps') ->
                       (match FStar_Tactics_Types.tracepoint
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Print.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (2))
                                         (Prims.of_int (63))
                                         (Prims.of_int (41)))))
                        with
                        | true ->
                            FStar_Tactics_Result.Success
                              ((paren a),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Print.fst"
                                            (Prims.of_int (63))
                                            (Prims.of_int (2))
                                            (Prims.of_int (63))
                                            (Prims.of_int (41))))))))
                   | FStar_Tactics_Result.Failed (e1, ps') ->
                       FStar_Tactics_Result.Failed (e1, ps'))))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (62)) (Prims.of_int (13))
                              (Prims.of_int (62)) (Prims.of_int (14))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Print.fst"
                        (Prims.of_int (62)) (Prims.of_int (2))
                        (Prims.of_int (63)) (Prims.of_int (41))))))
and (comp_to_ast_string :
  FStar_Reflection_Types.comp ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total (t, uu___) ->
        (fun ps ->
           match (term_to_ast_string t)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Print.fst"
                               (Prims.of_int (67)) (Prims.of_int (28))
                               (Prims.of_int (67)) (Prims.of_int (48))))))
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
                      ((Prims.strcat "Tot " a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | FStar_Reflection_Data.C_GTotal (t, uu___) ->
        (fun ps ->
           match (term_to_ast_string t)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Print.fst"
                               (Prims.of_int (68)) (Prims.of_int (30))
                               (Prims.of_int (68)) (Prims.of_int (50))))))
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
                      ((Prims.strcat "GTot " a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | FStar_Reflection_Data.C_Lemma (pre, post, uu___) ->
        (fun ps ->
           match match (term_to_ast_string pre)
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Print.fst"
                                           (Prims.of_int (69))
                                           (Prims.of_int (37))
                                           (Prims.of_int (69))
                                           (Prims.of_int (91))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Print.fst"
                                     (Prims.of_int (69)) (Prims.of_int (37))
                                     (Prims.of_int (69)) (Prims.of_int (59))))))
                 with
                 | FStar_Tactics_Result.Success (a, ps') ->
                     (match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range ps'
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (69))
                                       (Prims.of_int (37))
                                       (Prims.of_int (69))
                                       (Prims.of_int (91)))))
                      with
                      | true ->
                          (match match (term_to_ast_string post)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Print.fst"
                                                                 (Prims.of_int (69))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (69))
                                                                 (Prims.of_int (91))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Print.fst"
                                                           (Prims.of_int (69))
                                                           (Prims.of_int (62))
                                                           (Prims.of_int (69))
                                                           (Prims.of_int (91))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Print.fst"
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (68))
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (91))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps'1) ->
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
                                            ((Prims.strcat " " a1),
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
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (603))
                                                 (Prims.of_int (31)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ((Prims.strcat a a1),
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
                      ((Prims.strcat "Lemma " a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | FStar_Reflection_Data.C_Eff (uu___, eff, res, uu___1) ->
        (fun ps ->
           match match match match (term_to_ast_string res)
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
                                                                   "FStar.Tactics.Print.fst"
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (37))
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (91))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Print.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (43))
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (91))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Print.fst"
                                                       (Prims.of_int (70))
                                                       (Prims.of_int (61))
                                                       (Prims.of_int (70))
                                                       (Prims.of_int (90))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (70))
                                                 (Prims.of_int (68))
                                                 (Prims.of_int (70))
                                                 (Prims.of_int (90))))))
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
                                        ((Prims.strcat ", " a),
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
                                  ((Prims.strcat
                                      (FStar_Reflection_Builtins.implode_qn
                                         eff) a),
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
                                    (Prims.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (70))
                                       (Prims.of_int (37))
                                       (Prims.of_int (70))
                                       (Prims.of_int (91)))))
                      with
                      | true ->
                          FStar_Tactics_Result.Success
                            ((paren a),
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Print.fst"
                                          (Prims.of_int (70))
                                          (Prims.of_int (37))
                                          (Prims.of_int (70))
                                          (Prims.of_int (91))))))))
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
                      ((Prims.strcat "Effect " a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "prims.fst"
                                    (Prims.of_int (603)) (Prims.of_int (19))
                                    (Prims.of_int (603)) (Prims.of_int (31))))))))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
and (const_to_ast_string :
  FStar_Reflection_Data.vconst ->
    FStar_Tactics_Types.proofstate ->
      Prims.string FStar_Tactics_Result.__result)
  =
  fun c ->
    fun s ->
      FStar_Tactics_Result.Success
        ((match c with
          | FStar_Reflection_Data.C_Unit -> "C_Unit"
          | FStar_Reflection_Data.C_Int i ->
              Prims.strcat "C_Int " (Prims.string_of_int i)
          | FStar_Reflection_Data.C_True -> "C_True"
          | FStar_Reflection_Data.C_False -> "C_False"
          | FStar_Reflection_Data.C_String s1 -> Prims.strcat "C_String " s1
          | FStar_Reflection_Data.C_Range uu___ -> "C_Range _"
          | FStar_Reflection_Data.C_Reify -> "C_Reify"
          | FStar_Reflection_Data.C_Reflect name ->
              Prims.strcat "C_Reflect "
                (FStar_Reflection_Builtins.implode_qn name)), s)