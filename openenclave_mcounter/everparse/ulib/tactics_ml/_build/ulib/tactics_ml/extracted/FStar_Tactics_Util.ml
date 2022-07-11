open Prims
let rec map :
  'a 'b .
    ('a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          'b Prims.list FStar_Tactics_Result.__result
  =
  fun f ->
    fun x ->
      match x with
      | [] -> (fun s -> FStar_Tactics_Result.Success ([], s))
      | a1::tl ->
          (fun ps ->
             match (f a1)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (28)) (Prims.of_int (13))
                                 (Prims.of_int (28)) (Prims.of_int (16))))))
             with
             | FStar_Tactics_Result.Success (a2, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (28)) (Prims.of_int (16))
                                   (Prims.of_int (28)) (Prims.of_int (18)))))
                  with
                  | true ->
                      (match (map f tl)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Util.fst"
                                                 (Prims.of_int (28))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (28))
                                                 (Prims.of_int (18))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (28))
                                           (Prims.of_int (18))
                                           (Prims.of_int (28))
                                           (Prims.of_int (26))))))
                       with
                       | FStar_Tactics_Result.Success (a3, ps'1) ->
                           (match FStar_Tactics_Types.tracepoint
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Util.fst"
                                             (Prims.of_int (28))
                                             (Prims.of_int (16))
                                             (Prims.of_int (28))
                                             (Prims.of_int (18)))))
                            with
                            | true ->
                                FStar_Tactics_Result.Success
                                  ((a2 :: a3),
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Util.fst"
                                                (Prims.of_int (28))
                                                (Prims.of_int (16))
                                                (Prims.of_int (28))
                                                (Prims.of_int (18))))))))
                       | FStar_Tactics_Result.Failed (e, ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec __mapi :
  'a 'b .
    Prims.nat ->
      (Prims.nat ->
         'a ->
           FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
        ->
        'a Prims.list ->
          FStar_Tactics_Types.proofstate ->
            'b Prims.list FStar_Tactics_Result.__result
  =
  fun i ->
    fun f ->
      fun x ->
        match x with
        | [] -> (fun s -> FStar_Tactics_Result.Success ([], s))
        | a1::tl ->
            (fun ps ->
               match (f i a1)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (35)) (Prims.of_int (13))
                                   (Prims.of_int (35)) (Prims.of_int (18))))))
               with
               | FStar_Tactics_Result.Success (a2, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Util.fst"
                                     (Prims.of_int (35)) (Prims.of_int (18))
                                     (Prims.of_int (35)) (Prims.of_int (20)))))
                    with
                    | true ->
                        (match (__mapi (i + Prims.int_one) f tl)
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Util.fst"
                                                   (Prims.of_int (35))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (35))
                                                   (Prims.of_int (20))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Util.fst"
                                             (Prims.of_int (35))
                                             (Prims.of_int (20))
                                             (Prims.of_int (35))
                                             (Prims.of_int (37))))))
                         with
                         | FStar_Tactics_Result.Success (a3, ps'1) ->
                             (match FStar_Tactics_Types.tracepoint
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Util.fst"
                                               (Prims.of_int (35))
                                               (Prims.of_int (18))
                                               (Prims.of_int (35))
                                               (Prims.of_int (20)))))
                              with
                              | true ->
                                  FStar_Tactics_Result.Success
                                    ((a2 :: a3),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Util.fst"
                                                  (Prims.of_int (35))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (35))
                                                  (Prims.of_int (20))))))))
                         | FStar_Tactics_Result.Failed (e, ps'1) ->
                             FStar_Tactics_Result.Failed (e, ps'1)))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let mapi :
  'a 'b .
    (Prims.nat ->
       'a ->
         FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          'b Prims.list FStar_Tactics_Result.__result
  = fun f -> fun l -> __mapi Prims.int_zero f l
let rec iter :
  'a .
    ('a ->
       FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun f ->
    fun x ->
      match x with
      | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
      | a1::tl ->
          (fun ps ->
             match (f a1)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (45)) (Prims.of_int (13))
                                 (Prims.of_int (45)) (Prims.of_int (16))))))
             with
             | FStar_Tactics_Result.Success (a2, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (45)) (Prims.of_int (18))
                                   (Prims.of_int (45)) (Prims.of_int (27)))))
                  with
                  | true ->
                      (iter f tl)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Util.fst"
                                    (Prims.of_int (45)) (Prims.of_int (18))
                                    (Prims.of_int (45)) (Prims.of_int (27)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec iteri_aux :
  'a .
    Prims.int ->
      (Prims.int ->
         'a ->
           FStar_Tactics_Types.proofstate ->
             unit FStar_Tactics_Result.__result)
        ->
        'a Prims.list ->
          FStar_Tactics_Types.proofstate ->
            unit FStar_Tactics_Result.__result
  =
  fun i ->
    fun f ->
      fun x ->
        match x with
        | [] -> (fun s -> FStar_Tactics_Result.Success ((), s))
        | a1::tl ->
            (fun ps ->
               match (f i a1)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (52)) (Prims.of_int (13))
                                   (Prims.of_int (52)) (Prims.of_int (18))))))
               with
               | FStar_Tactics_Result.Success (a2, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Util.fst"
                                     (Prims.of_int (52)) (Prims.of_int (20))
                                     (Prims.of_int (52)) (Prims.of_int (40)))))
                    with
                    | true ->
                        (iteri_aux (i + Prims.int_one) f tl)
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (52)) (Prims.of_int (20))
                                      (Prims.of_int (52)) (Prims.of_int (40)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let iteri :
  'a .
    (Prims.int ->
       'a ->
         FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  = fun f -> fun x -> iteri_aux Prims.int_zero f x
let rec fold_left :
  'a 'b .
    ('a ->
       'b ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      'a ->
        'b Prims.list ->
          FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun f ->
    fun x ->
      fun l ->
        match l with
        | [] -> (fun s -> FStar_Tactics_Result.Success (x, s))
        | hd::tl ->
            (fun ps ->
               match (f x hd)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (62)) (Prims.of_int (26))
                                   (Prims.of_int (62)) (Prims.of_int (34))))))
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Util.fst"
                                     (Prims.of_int (62)) (Prims.of_int (14))
                                     (Prims.of_int (62)) (Prims.of_int (37)))))
                    with
                    | true ->
                        (fold_left f a1 tl)
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (62)) (Prims.of_int (14))
                                      (Prims.of_int (62)) (Prims.of_int (37)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let rec fold_right :
  'a 'b .
    ('a ->
       'b ->
         FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        'b ->
          FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
  =
  fun f ->
    fun l ->
      fun x ->
        match l with
        | [] -> (fun s -> FStar_Tactics_Result.Success (x, s))
        | hd::tl ->
            (fun ps ->
               match (fold_right f tl x)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (69)) (Prims.of_int (19))
                                   (Prims.of_int (69)) (Prims.of_int (38))))))
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Util.fst"
                                     (Prims.of_int (69)) (Prims.of_int (14))
                                     (Prims.of_int (69)) (Prims.of_int (38)))))
                    with
                    | true ->
                        (f hd a1)
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (69)) (Prims.of_int (14))
                                      (Prims.of_int (69)) (Prims.of_int (38)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        FStar_Tactics_Types.proofstate ->
          ('a * 'b) Prims.list FStar_Tactics_Result.__result
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (x::xs, y::ys) ->
          (fun ps ->
             match (zip xs ys)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (76)) (Prims.of_int (31))
                                 (Prims.of_int (76)) (Prims.of_int (42))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (76)) (Prims.of_int (28))
                                   (Prims.of_int (76)) (Prims.of_int (30)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        (((x, y) :: a1),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (76)) (Prims.of_int (28))
                                      (Prims.of_int (76)) (Prims.of_int (30))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | uu___ -> (fun s -> FStar_Tactics_Result.Success ([], s))
let rec filter :
  'a .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         Prims.bool FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          'a Prims.list FStar_Tactics_Result.__result
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> (fun s -> FStar_Tactics_Result.Success ([], s))
      | hd::tl ->
          (fun ps ->
             match (f hd)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (84)) (Prims.of_int (17))
                                 (Prims.of_int (84)) (Prims.of_int (21))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (84)) (Prims.of_int (14))
                                   (Prims.of_int (84)) (Prims.of_int (61)))))
                  with
                  | true ->
                      (if a1
                       then
                         (fun ps1 ->
                            match (filter f tl)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Util.fst"
                                                (Prims.of_int (84))
                                                (Prims.of_int (31))
                                                (Prims.of_int (84))
                                                (Prims.of_int (44))))))
                            with
                            | FStar_Tactics_Result.Success (a2, ps'1) ->
                                (match FStar_Tactics_Types.tracepoint
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Util.fst"
                                                  (Prims.of_int (84))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (84))
                                                  (Prims.of_int (31)))))
                                 with
                                 | true ->
                                     FStar_Tactics_Result.Success
                                       ((hd :: a2),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Util.fst"
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (29))
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (31))))))))
                            | FStar_Tactics_Result.Failed (e, ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1))
                       else filter f tl)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Util.fst"
                                    (Prims.of_int (84)) (Prims.of_int (14))
                                    (Prims.of_int (84)) (Prims.of_int (61)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let rec filter_map_acc :
  'a 'b .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
      ->
      'b Prims.list ->
        'a Prims.list ->
          FStar_Tactics_Types.proofstate ->
            'b Prims.list FStar_Tactics_Result.__result
  =
  fun f ->
    fun acc ->
      fun l ->
        match l with
        | [] ->
            (fun s ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.rev acc), s))
        | hd::tl ->
            (fun ps ->
               match (f hd)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (94)) (Prims.of_int (12))
                                   (Prims.of_int (94)) (Prims.of_int (16))))))
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Util.fst"
                                     (Prims.of_int (94)) (Prims.of_int (6))
                                     (Prims.of_int (98)) (Prims.of_int (33)))))
                    with
                    | true ->
                        ((match a1 with
                          | FStar_Pervasives_Native.Some hd1 ->
                              filter_map_acc f (hd1 :: acc) tl
                          | FStar_Pervasives_Native.None ->
                              filter_map_acc f acc tl))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (94)) (Prims.of_int (6))
                                      (Prims.of_int (98)) (Prims.of_int (33)))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let filter_map :
  'a 'b .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          'b Prims.list FStar_Tactics_Result.__result
  = fun f -> fun l -> filter_map_acc f [] l
let rec tryPick :
  'a 'b .
    ('a ->
       FStar_Tactics_Types.proofstate ->
         'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result)
      ->
      'a Prims.list ->
        FStar_Tactics_Types.proofstate ->
          'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result
  =
  fun f ->
    fun l ->
      match l with
      | [] ->
          (fun s ->
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
      | hd::tl ->
          (fun ps ->
             match (f hd)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (109)) (Prims.of_int (13))
                                 (Prims.of_int (109)) (Prims.of_int (17))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (109)) (Prims.of_int (7))
                                   (Prims.of_int (111)) (Prims.of_int (31)))))
                  with
                  | true ->
                      ((match a1 with
                        | FStar_Pervasives_Native.Some x ->
                            (fun s ->
                               FStar_Tactics_Result.Success
                                 ((FStar_Pervasives_Native.Some x), s))
                        | FStar_Pervasives_Native.None -> tryPick f tl))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Util.fst"
                                    (Prims.of_int (109)) (Prims.of_int (7))
                                    (Prims.of_int (111)) (Prims.of_int (31)))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
let map_opt :
  'a 'b .
    ('a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result)
      ->
      'a FStar_Pervasives_Native.option ->
        FStar_Tactics_Types.proofstate ->
          'b FStar_Pervasives_Native.option FStar_Tactics_Result.__result
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None ->
          (fun s ->
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
      | FStar_Pervasives_Native.Some x1 ->
          (fun ps ->
             match (f x1)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (117)) (Prims.of_int (19))
                                 (Prims.of_int (117)) (Prims.of_int (24))))))
             with
             | FStar_Tactics_Result.Success (a1, ps') ->
                 (match FStar_Tactics_Types.tracepoint
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (117)) (Prims.of_int (14))
                                   (Prims.of_int (117)) (Prims.of_int (24)))))
                  with
                  | true ->
                      FStar_Tactics_Result.Success
                        ((FStar_Pervasives_Native.Some a1),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (117))
                                      (Prims.of_int (14))
                                      (Prims.of_int (117))
                                      (Prims.of_int (24))))))))
             | FStar_Tactics_Result.Failed (e, ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))