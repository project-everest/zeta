open Prims

type ('a, 'cmuadd, 'cmumult) distribute_left_lemma = unit
type ('a, 'cmuadd, 'cmumult) distribute_right_lemma = unit
type ('a, 'cmuadd, 'cmumult) mult_zero_l_lemma = unit
type ('a, 'cmuadd, 'opp) add_opp_r_lemma = unit
type 'a cr =
  | CR of 'a FStar_Algebra_CommMonoid.cm * 'a FStar_Algebra_CommMonoid.cm *
  ('a -> 'a) * unit * unit * unit 
let uu___is_CR : 'a . 'a cr -> Prims.bool = fun projectee -> true
let __proj__CR__item__cm_add : 'a . 'a cr -> 'a FStar_Algebra_CommMonoid.cm =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_add
let __proj__CR__item__cm_mult : 'a . 'a cr -> 'a FStar_Algebra_CommMonoid.cm
  =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_mult
let __proj__CR__item__opp : 'a . 'a cr -> 'a -> 'a =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> opp




let norm_fully : 'a . 'a -> 'a = fun x -> x
type index = Prims.nat
type varlist =
  | Nil_var 
  | Cons_var of index * varlist 
let (uu___is_Nil_var : varlist -> Prims.bool) =
  fun projectee -> match projectee with | Nil_var -> true | uu___ -> false
let (uu___is_Cons_var : varlist -> Prims.bool) =
  fun projectee ->
    match projectee with | Cons_var (_0, _1) -> true | uu___ -> false
let (__proj__Cons_var__item___0 : varlist -> index) =
  fun projectee -> match projectee with | Cons_var (_0, _1) -> _0
let (__proj__Cons_var__item___1 : varlist -> varlist) =
  fun projectee -> match projectee with | Cons_var (_0, _1) -> _1
type 'a canonical_sum =
  | Nil_monom 
  | Cons_monom of 'a * varlist * 'a canonical_sum 
  | Cons_varlist of varlist * 'a canonical_sum 
let uu___is_Nil_monom : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee -> match projectee with | Nil_monom -> true | uu___ -> false
let uu___is_Cons_monom : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee ->
    match projectee with | Cons_monom (_0, _1, _2) -> true | uu___ -> false
let __proj__Cons_monom__item___0 : 'a . 'a canonical_sum -> 'a =
  fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _0
let __proj__Cons_monom__item___1 : 'a . 'a canonical_sum -> varlist =
  fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _1
let __proj__Cons_monom__item___2 : 'a . 'a canonical_sum -> 'a canonical_sum
  = fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _2
let uu___is_Cons_varlist : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee ->
    match projectee with | Cons_varlist (_0, _1) -> true | uu___ -> false
let __proj__Cons_varlist__item___0 : 'a . 'a canonical_sum -> varlist =
  fun projectee -> match projectee with | Cons_varlist (_0, _1) -> _0
let __proj__Cons_varlist__item___1 :
  'a . 'a canonical_sum -> 'a canonical_sum =
  fun projectee -> match projectee with | Cons_varlist (_0, _1) -> _1
let rec (varlist_lt : varlist -> varlist -> Prims.bool) =
  fun x ->
    fun y ->
      match (x, y) with
      | (Nil_var, Cons_var (uu___, uu___1)) -> true
      | (Cons_var (i, xs), Cons_var (j, ys)) ->
          if i < j then true else (i = j) && (varlist_lt xs ys)
      | (uu___, uu___1) -> false
let rec (varlist_merge : varlist -> varlist -> varlist) =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (uu___, Nil_var) -> l1
      | (Nil_var, uu___) -> l2
      | (Cons_var (v1, t1), Cons_var (v2, t2)) -> vm_aux v1 t1 l2
and (vm_aux : index -> varlist -> varlist -> varlist) =
  fun v1 ->
    fun t1 ->
      fun l2 ->
        match l2 with
        | Cons_var (v2, t2) ->
            if v1 < v2
            then Cons_var (v1, (varlist_merge t1 l2))
            else Cons_var (v2, (vm_aux v1 t1 t2))
        | uu___ -> Cons_var (v1, t1)
let rec canonical_sum_merge :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun s1 ->
      fun s2 ->
        let aplus =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_add r) in
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r) in
        match s1 with
        | Cons_monom (c1, l1, t1) -> csm_aux r c1 l1 t1 s2
        | Cons_varlist (l1, t1) -> csm_aux r aone l1 t1 s2
        | Nil_monom -> s2
and csm_aux :
  'a .
    'a cr ->
      'a ->
        varlist -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum
  =
  fun r ->
    fun c1 ->
      fun l1 ->
        fun t1 ->
          fun s2 ->
            let aplus =
              FStar_Algebra_CommMonoid.__proj__CM__item__mult
                (__proj__CR__item__cm_add r) in
            let aone =
              FStar_Algebra_CommMonoid.__proj__CM__item__unit
                (__proj__CR__item__cm_mult r) in
            match s2 with
            | Cons_monom (c2, l2, t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 c2), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_monom (c2, l2, (csm_aux r c1 l1 t1 t2))
            | Cons_varlist (l2, t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 aone), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_varlist (l2, (csm_aux r c1 l1 t1 t2))
            | Nil_monom -> Cons_monom (c1, l1, t1)
let rec monom_insert :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c1 ->
      fun l1 ->
        fun s2 ->
          let aplus =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_add r) in
          let aone =
            FStar_Algebra_CommMonoid.__proj__CM__item__unit
              (__proj__CR__item__cm_mult r) in
          match s2 with
          | Cons_monom (c2, l2, t2) ->
              if l1 = l2
              then Cons_monom ((aplus c1 c2), l1, t2)
              else
                if varlist_lt l1 l2
                then Cons_monom (c1, l1, s2)
                else Cons_monom (c2, l2, (monom_insert r c1 l1 t2))
          | Cons_varlist (l2, t2) ->
              if l1 = l2
              then Cons_monom ((aplus c1 aone), l1, t2)
              else
                if varlist_lt l1 l2
                then Cons_monom (c1, l1, s2)
                else Cons_varlist (l2, (monom_insert r c1 l1 t2))
          | Nil_monom ->
              if c1 = aone
              then Cons_varlist (l1, Nil_monom)
              else Cons_monom (c1, l1, Nil_monom)
let varlist_insert :
  'a . 'a cr -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun l1 ->
      fun s2 ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r) in
        monom_insert r aone l1 s2
let rec canonical_sum_scalar :
  'a . 'a cr -> 'a -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c0 ->
      fun s ->
        let amult =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_mult r) in
        match s with
        | Cons_monom (c, l, t) ->
            Cons_monom ((amult c0 c), l, (canonical_sum_scalar r c0 t))
        | Cons_varlist (l, t) ->
            Cons_monom (c0, l, (canonical_sum_scalar r c0 t))
        | Nil_monom -> Nil_monom
let rec canonical_sum_scalar2 :
  'a . 'a cr -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun l0 ->
      fun s ->
        match s with
        | Cons_monom (c, l, t) ->
            monom_insert r c (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Cons_varlist (l, t) ->
            varlist_insert r (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Nil_monom -> Nil_monom
let rec canonical_sum_scalar3 :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c0 ->
      fun l0 ->
        fun s ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r) in
          match s with
          | Cons_monom (c, l, t) ->
              monom_insert r (amult c0 c) (varlist_merge l0 l)
                (canonical_sum_scalar3 r c0 l0 t)
          | Cons_varlist (l, t) ->
              monom_insert r c0 (varlist_merge l0 l)
                (canonical_sum_scalar3 r c0 l0 t)
          | Nil_monom -> s
let rec canonical_sum_prod :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | Cons_monom (c1, l1, t1) ->
            canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
              (canonical_sum_prod r t1 s2)
        | Cons_varlist (l1, t1) ->
            canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
              (canonical_sum_prod r t1 s2)
        | Nil_monom -> s1
type 'a spolynomial =
  | SPvar of index 
  | SPconst of 'a 
  | SPplus of 'a spolynomial * 'a spolynomial 
  | SPmult of 'a spolynomial * 'a spolynomial 
let uu___is_SPvar : 'a . 'a spolynomial -> Prims.bool =
  fun projectee -> match projectee with | SPvar _0 -> true | uu___ -> false
let __proj__SPvar__item___0 : 'a . 'a spolynomial -> index =
  fun projectee -> match projectee with | SPvar _0 -> _0
let uu___is_SPconst : 'a . 'a spolynomial -> Prims.bool =
  fun projectee -> match projectee with | SPconst _0 -> true | uu___ -> false
let __proj__SPconst__item___0 : 'a . 'a spolynomial -> 'a =
  fun projectee -> match projectee with | SPconst _0 -> _0
let uu___is_SPplus : 'a . 'a spolynomial -> Prims.bool =
  fun projectee ->
    match projectee with | SPplus (_0, _1) -> true | uu___ -> false
let __proj__SPplus__item___0 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPplus (_0, _1) -> _0
let __proj__SPplus__item___1 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPplus (_0, _1) -> _1
let uu___is_SPmult : 'a . 'a spolynomial -> Prims.bool =
  fun projectee ->
    match projectee with | SPmult (_0, _1) -> true | uu___ -> false
let __proj__SPmult__item___0 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPmult (_0, _1) -> _0
let __proj__SPmult__item___1 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPmult (_0, _1) -> _1
let rec spolynomial_normalize :
  'a . 'a cr -> 'a spolynomial -> 'a canonical_sum =
  fun r ->
    fun p ->
      match p with
      | SPvar i -> Cons_varlist ((Cons_var (i, Nil_var)), Nil_monom)
      | SPconst c -> Cons_monom (c, Nil_var, Nil_monom)
      | SPplus (l, q) ->
          canonical_sum_merge r (spolynomial_normalize r l)
            (spolynomial_normalize r q)
      | SPmult (l, q) ->
          canonical_sum_prod r (spolynomial_normalize r l)
            (spolynomial_normalize r q)
let rec canonical_sum_simplify :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun s ->
      let azero =
        FStar_Algebra_CommMonoid.__proj__CM__item__unit
          (__proj__CR__item__cm_add r) in
      let aone =
        FStar_Algebra_CommMonoid.__proj__CM__item__unit
          (__proj__CR__item__cm_mult r) in
      let aplus =
        FStar_Algebra_CommMonoid.__proj__CM__item__mult
          (__proj__CR__item__cm_add r) in
      match s with
      | Cons_monom (c, l, t) ->
          if c = azero
          then canonical_sum_simplify r t
          else
            if c = aone
            then Cons_varlist (l, (canonical_sum_simplify r t))
            else Cons_monom (c, l, (canonical_sum_simplify r t))
      | Cons_varlist (l, t) -> Cons_varlist (l, (canonical_sum_simplify r t))
      | Nil_monom -> s
let spolynomial_simplify : 'a . 'a cr -> 'a spolynomial -> 'a canonical_sum =
  fun r -> fun p -> canonical_sum_simplify r (spolynomial_normalize r p)
type 'a vmap = ((FStar_Reflection_Data.var * 'a) Prims.list * 'a)
let update : 'a . FStar_Reflection_Data.var -> 'a -> 'a vmap -> 'a vmap =
  fun x ->
    fun xa ->
      fun vm ->
        let uu___ = vm in match uu___ with | (l, y) -> (((x, xa) :: l), y)
let rec quote_list :
  'a .
    FStar_Reflection_Types.term ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           FStar_Reflection_Types.term FStar_Tactics_Result.__result)
        ->
        'a Prims.list ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.term FStar_Tactics_Result.__result
  =
  fun ta ->
    fun quotea ->
      fun xs ->
        match xs with
        | [] ->
            (fun s ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Derived.mk_app
                     (FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["Prims"; "Nil"])))
                     [(ta, FStar_Reflection_Data.Q_Implicit)]), s))
        | x::xs' ->
            (fun ps ->
               match match match match (quotea x)
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
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (68))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (380))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (382))
                                                                 (Prims.of_int (68))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (381))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (381))
                                                           (Prims.of_int (51))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (381))
                                                     (Prims.of_int (30))
                                                     (Prims.of_int (381))
                                                     (Prims.of_int (38))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (381))
                                                       (Prims.of_int (29))
                                                       (Prims.of_int (381))
                                                       (Prims.of_int (51)))))
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
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (381))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (381))
                                                          (Prims.of_int (51))))))))
                                 | FStar_Tactics_Result.Failed (e, ps') ->
                                     FStar_Tactics_Result.Failed (e, ps')
                           with
                           | FStar_Tactics_Result.Success (a1, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (380))
                                                 (Prims.of_int (29))
                                                 (Prims.of_int (382))
                                                 (Prims.of_int (68)))))
                                with
                                | true ->
                                    (match match match (quote_list ta quotea
                                                          xs')
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (67))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (54))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a2, ps'1) ->
                                                     (match FStar_Tactics_Types.tracepoint
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'1
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (67)))))
                                                      with
                                                      | true ->
                                                          FStar_Tactics_Result.Success
                                                            ((a2,
                                                               FStar_Reflection_Data.Q_Explicit),
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (67))))))))
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
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (380))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (382))
                                                                 (Prims.of_int (68)))))
                                                with
                                                | true ->
                                                    FStar_Tactics_Result.Success
                                                      ([a2],
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (68))))))))
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
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (380))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (382))
                                                           (Prims.of_int (68)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ((a1 :: a2),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (380))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (382))
                                                              (Prims.of_int (68))))))))
                                     | FStar_Tactics_Result.Failed (e, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e, ps') ->
                               FStar_Tactics_Result.Failed (e, ps')
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (380))
                                           (Prims.of_int (29))
                                           (Prims.of_int (382))
                                           (Prims.of_int (68)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (((ta, FStar_Reflection_Data.Q_Implicit) ::
                                  a1),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (380))
                                              (Prims.of_int (29))
                                              (Prims.of_int (382))
                                              (Prims.of_int (68))))))))
                     | FStar_Tactics_Result.Failed (e, ps') ->
                         FStar_Tactics_Result.Failed (e, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (380)) (Prims.of_int (14))
                                     (Prims.of_int (382)) (Prims.of_int (68)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["Prims"; "Cons"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (380))
                                        (Prims.of_int (14))
                                        (Prims.of_int (382))
                                        (Prims.of_int (68))))))))
               | FStar_Tactics_Result.Failed (e, ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
let quote_vm :
  'a .
    FStar_Reflection_Types.term ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           FStar_Reflection_Types.term FStar_Tactics_Result.__result)
        ->
        'a vmap ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.term FStar_Tactics_Result.__result
  =
  fun ta ->
    fun quotea ->
      fun vm ->
        fun ps ->
          match FStar_Tactics_Types.tracepoint
                  (FStar_Tactics_Types.set_proofstate_range
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.CanonCommSemiring.fst"
                                 (Prims.of_int (387)) (Prims.of_int (4))
                                 (Prims.of_int (389)) (Prims.of_int (35))))))
                     (FStar_Range.prims_to_fstar_range
                        (Prims.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                           (Prims.of_int (390)) (Prims.of_int (2))
                           (Prims.of_int (394)) (Prims.of_int (73)))))
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
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (387))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (389))
                                                  (Prims.of_int (35))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (390))
                                            (Prims.of_int (2))
                                            (Prims.of_int (394))
                                            (Prims.of_int (73))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (390))
                                      (Prims.of_int (16))
                                      (Prims.of_int (390))
                                      (Prims.of_int (47))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommSemiring.fst"
                                (Prims.of_int (391)) (Prims.of_int (2))
                                (Prims.of_int (394)) (Prims.of_int (73)))))
               with
               | true ->
                   (match (quote_list
                             (FStar_Reflection_Derived.mk_e_app
                                (FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Builtins.pack_fv
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"])))
                                [FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Builtins.pack_fv
                                         ["Prims"; "nat"]));
                                ta])
                             (fun p ->
                                fun ps1 ->
                                  match match match match match (FStar_Tactics_Builtins.pack
                                                                   (FStar_Reflection_Data.Tv_Const
                                                                    (FStar_Reflection_Data.C_Int
                                                                    (FStar_Pervasives_Native.fst
                                                                    p))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (38))))))
                                                          with
                                                          | FStar_Tactics_Result.Success
                                                              (a1, ps') ->
                                                              (match 
                                                                 FStar_Tactics_Types.tracepoint
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (51)))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (51))))))))
                                                          | FStar_Tactics_Result.Failed
                                                              (e, ps') ->
                                                              FStar_Tactics_Result.Failed
                                                                (e, ps')
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a1, ps') ->
                                                        (match FStar_Tactics_Types.tracepoint
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35)))))
                                                         with
                                                         | true ->
                                                             (match match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.snd
                                                                    p))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (21))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (34)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (34))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a2, ps'1)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1 ::
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1)))
                                                    | FStar_Tactics_Result.Failed
                                                        (e, ps') ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps')
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a1, ps') ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35)))))
                                                   with
                                                   | true ->
                                                       FStar_Tactics_Result.Success
                                                         (((ta,
                                                             FStar_Reflection_Data.Q_Implicit)
                                                           :: a1),
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (35))))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps') ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps')
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a1, ps') ->
                                            (match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (387))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (389))
                                                              (Prims.of_int (35)))))
                                             with
                                             | true ->
                                                 FStar_Tactics_Result.Success
                                                   ((((FStar_Reflection_Builtins.pack_ln
                                                         (FStar_Reflection_Data.Tv_FVar
                                                            (FStar_Reflection_Builtins.pack_fv
                                                               ["Prims";
                                                               "nat"]))),
                                                       FStar_Reflection_Data.Q_Implicit)
                                                     :: a1),
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (387))
                                                                 (Prims.of_int (23))
                                                                 (Prims.of_int (389))
                                                                 (Prims.of_int (35))))))))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps') ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps')
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps') ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (387))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (389))
                                                        (Prims.of_int (35)))))
                                       with
                                       | true ->
                                           FStar_Tactics_Result.Success
                                             ((FStar_Reflection_Derived.mk_app
                                                 (FStar_Reflection_Builtins.pack_ln
                                                    (FStar_Reflection_Data.Tv_FVar
                                                       (FStar_Reflection_Builtins.pack_fv
                                                          ["FStar";
                                                          "Pervasives";
                                                          "Native";
                                                          "Mktuple2"]))) a1),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (387))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (389))
                                                           (Prims.of_int (35))))))))
                                  | FStar_Tactics_Result.Failed (e, ps') ->
                                      FStar_Tactics_Result.Failed (e, ps'))
                             (FStar_Pervasives_Native.fst vm))
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
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (387))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (389))
                                                                (Prims.of_int (35))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (390))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (394))
                                                          (Prims.of_int (73))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (47))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (391))
                                              (Prims.of_int (2))
                                              (Prims.of_int (394))
                                              (Prims.of_int (73))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (391))
                                        (Prims.of_int (14))
                                        (Prims.of_int (391))
                                        (Prims.of_int (57))))))
                    with
                    | FStar_Tactics_Result.Success (a1, ps') ->
                        (match FStar_Tactics_Types.tracepoint
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (392))
                                          (Prims.of_int (2))
                                          (Prims.of_int (394))
                                          (Prims.of_int (73)))))
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
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (392))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (394))
                                                           (Prims.of_int (73))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (392))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (392))
                                                     (Prims.of_int (41))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (393))
                                               (Prims.of_int (2))
                                               (Prims.of_int (394))
                                               (Prims.of_int (73)))))
                              with
                              | true ->
                                  (match match match match match match 
                                                                   (quotea
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (72))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (59))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (72)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (72))))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a2, ps'1) ->
                                                               (match 
                                                                  FStar_Tactics_Types.tracepoint
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73)))))
                                                                with
                                                                | true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73)))))
                                                          with
                                                          | true ->
                                                              FStar_Tactics_Result.Success
                                                                (((a1,
                                                                    FStar_Reflection_Data.Q_Explicit)
                                                                  :: a2),
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73)))))
                                                    with
                                                    | true ->
                                                        FStar_Tactics_Result.Success
                                                          (((ta,
                                                              FStar_Reflection_Data.Q_Implicit)
                                                            :: a2),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (73))))))))
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
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (393))
                                                               (Prims.of_int (21))
                                                               (Prims.of_int (394))
                                                               (Prims.of_int (73)))))
                                              with
                                              | true ->
                                                  FStar_Tactics_Result.Success
                                                    ((((FStar_Reflection_Derived.mk_e_app
                                                          (FStar_Reflection_Builtins.pack_ln
                                                             (FStar_Reflection_Data.Tv_FVar
                                                                (FStar_Reflection_Builtins.pack_fv
                                                                   ["Prims";
                                                                   "list"])))
                                                          [FStar_Reflection_Derived.mk_e_app
                                                             (FStar_Reflection_Builtins.pack_ln
                                                                (FStar_Reflection_Data.Tv_FVar
                                                                   (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                             [FStar_Reflection_Builtins.pack_ln
                                                                (FStar_Reflection_Data.Tv_FVar
                                                                   (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "nat"]));
                                                             ta]]),
                                                        FStar_Reflection_Data.Q_Implicit)
                                                      :: a2),
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (393))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (394))
                                                                  (Prims.of_int (73))))))))
                                         | FStar_Tactics_Result.Failed
                                             (e, ps'1) ->
                                             FStar_Tactics_Result.Failed
                                               (e, ps'1)
                                   with
                                   | FStar_Tactics_Result.Success (a2, ps'1)
                                       ->
                                       (match FStar_Tactics_Types.tracepoint
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommSemiring.fst"
                                                         (Prims.of_int (393))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (394))
                                                         (Prims.of_int (73)))))
                                        with
                                        | true ->
                                            FStar_Tactics_Result.Success
                                              ((FStar_Reflection_Derived.mk_app
                                                  (FStar_Reflection_Builtins.pack_ln
                                                     (FStar_Reflection_Data.Tv_FVar
                                                        (FStar_Reflection_Builtins.pack_fv
                                                           ["FStar";
                                                           "Pervasives";
                                                           "Native";
                                                           "Mktuple2"]))) a2),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (393))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (394))
                                                            (Prims.of_int (73))))))))
                                   | FStar_Tactics_Result.Failed (e, ps'1) ->
                                       FStar_Tactics_Result.Failed (e, ps'1))))
                    | FStar_Tactics_Result.Failed (e, ps') ->
                        FStar_Tactics_Result.Failed (e, ps')))
let interp_var : 'a . 'a vmap -> index -> 'a =
  fun vm ->
    fun i ->
      match FStar_List_Tot_Base.assoc i (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some x -> x
      | uu___ -> FStar_Pervasives_Native.snd vm
let rec ivl_aux : 'a . 'a cr -> 'a vmap -> index -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun x ->
        fun t ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r) in
          match t with
          | Nil_var -> interp_var vm x
          | Cons_var (x', t') -> amult (interp_var vm x) (ivl_aux r vm x' t')
let interp_vl : 'a . 'a cr -> 'a vmap -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun l ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r) in
        match l with | Nil_var -> aone | Cons_var (x, t) -> ivl_aux r vm x t
let interp_m : 'a . 'a cr -> 'a vmap -> 'a -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun c ->
        fun l ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r) in
          match l with
          | Nil_var -> c
          | Cons_var (x, t) -> amult c (ivl_aux r vm x t)
let rec ics_aux : 'a . 'a cr -> 'a vmap -> 'a -> 'a canonical_sum -> 'a =
  fun r ->
    fun vm ->
      fun x ->
        fun s ->
          let aplus =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_add r) in
          match s with
          | Nil_monom -> x
          | Cons_varlist (l, t) ->
              aplus x (ics_aux r vm (interp_vl r vm l) t)
          | Cons_monom (c, l, t) ->
              aplus x (ics_aux r vm (interp_m r vm c l) t)
let interp_cs : 'a . 'a cr -> 'a vmap -> 'a canonical_sum -> 'a =
  fun r ->
    fun vm ->
      fun s ->
        let azero =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_add r) in
        match s with
        | Nil_monom -> azero
        | Cons_varlist (l, t) -> ics_aux r vm (interp_vl r vm l) t
        | Cons_monom (c, l, t) -> ics_aux r vm (interp_m r vm c l) t
let rec interp_sp : 'a . 'a cr -> 'a vmap -> 'a spolynomial -> 'a =
  fun r ->
    fun vm ->
      fun p ->
        let aplus =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_add r) in
        let amult =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_mult r) in
        match p with
        | SPconst c -> c
        | SPvar i -> interp_var vm i
        | SPplus (p1, p2) -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
        | SPmult (p1, p2) -> amult (interp_sp r vm p1) (interp_sp r vm p2)























type 'a polynomial =
  | Pvar of index 
  | Pconst of 'a 
  | Pplus of 'a polynomial * 'a polynomial 
  | Pmult of 'a polynomial * 'a polynomial 
  | Popp of 'a polynomial 
let uu___is_Pvar : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Pvar _0 -> true | uu___ -> false
let __proj__Pvar__item___0 : 'a . 'a polynomial -> index =
  fun projectee -> match projectee with | Pvar _0 -> _0
let uu___is_Pconst : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Pconst _0 -> true | uu___ -> false
let __proj__Pconst__item___0 : 'a . 'a polynomial -> 'a =
  fun projectee -> match projectee with | Pconst _0 -> _0
let uu___is_Pplus : 'a . 'a polynomial -> Prims.bool =
  fun projectee ->
    match projectee with | Pplus (_0, _1) -> true | uu___ -> false
let __proj__Pplus__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pplus (_0, _1) -> _0
let __proj__Pplus__item___1 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pplus (_0, _1) -> _1
let uu___is_Pmult : 'a . 'a polynomial -> Prims.bool =
  fun projectee ->
    match projectee with | Pmult (_0, _1) -> true | uu___ -> false
let __proj__Pmult__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pmult (_0, _1) -> _0
let __proj__Pmult__item___1 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pmult (_0, _1) -> _1
let uu___is_Popp : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Popp _0 -> true | uu___ -> false
let __proj__Popp__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Popp _0 -> _0
let rec polynomial_normalize :
  'a . 'a cr -> 'a polynomial -> 'a canonical_sum =
  fun r ->
    fun p ->
      match p with
      | Pvar i -> Cons_varlist ((Cons_var (i, Nil_var)), Nil_monom)
      | Pconst c -> Cons_monom (c, Nil_var, Nil_monom)
      | Pplus (l, q) ->
          canonical_sum_merge r (polynomial_normalize r l)
            (polynomial_normalize r q)
      | Pmult (l, q) ->
          canonical_sum_prod r (polynomial_normalize r l)
            (polynomial_normalize r q)
      | Popp p1 ->
          canonical_sum_scalar3 r
            (__proj__CR__item__opp r
               (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                  (__proj__CR__item__cm_mult r))) Nil_var
            (polynomial_normalize r p1)
let polynomial_simplify : 'a . 'a cr -> 'a polynomial -> 'a canonical_sum =
  fun r -> fun p -> canonical_sum_simplify r (polynomial_normalize r p)
let rec spolynomial_of : 'a . 'a cr -> 'a polynomial -> 'a spolynomial =
  fun r ->
    fun p ->
      match p with
      | Pvar i -> SPvar i
      | Pconst c -> SPconst c
      | Pplus (l, q) -> SPplus ((spolynomial_of r l), (spolynomial_of r q))
      | Pmult (l, q) -> SPmult ((spolynomial_of r l), (spolynomial_of r q))
      | Popp p1 ->
          SPmult
            ((SPconst
                (__proj__CR__item__opp r
                   (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                      (__proj__CR__item__cm_mult r)))),
              (spolynomial_of r p1))
let rec interp_p : 'a . 'a cr -> 'a vmap -> 'a polynomial -> 'a =
  fun r ->
    fun vm ->
      fun p ->
        let aplus =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_add r) in
        let amult =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_mult r) in
        match p with
        | Pconst c -> c
        | Pvar i -> interp_var vm i
        | Pplus (p1, p2) -> aplus (interp_p r vm p1) (interp_p r vm p2)
        | Pmult (p1, p2) -> amult (interp_p r vm p1) (interp_p r vm p2)
        | Popp p1 -> __proj__CR__item__opp r (interp_p r vm p1)



let (ddump :
  Prims.string ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun m ->
    fun ps ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                          (Prims.of_int (1496)) (Prims.of_int (17))
                          (Prims.of_int (1496)) (Prims.of_int (29))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommSemiring.fst"
                            (Prims.of_int (1496)) (Prims.of_int (14))
                            (Prims.of_int (1496)) (Prims.of_int (41)))))
           with
           | true ->
               (if a
                then FStar_Tactics_Builtins.dump m
                else (fun s -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1496)) (Prims.of_int (14))
                             (Prims.of_int (1496)) (Prims.of_int (41)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (find_aux :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        Prims.nat FStar_Pervasives_Native.option)
  =
  fun n ->
    fun x ->
      fun xs ->
        match xs with
        | [] -> FStar_Pervasives_Native.None
        | x'::xs' ->
            if FStar_Reflection_Builtins.term_eq x x'
            then FStar_Pervasives_Native.Some n
            else find_aux (n + Prims.int_one) x xs'
let (find :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      Prims.nat FStar_Pervasives_Native.option)
  = find_aux Prims.int_zero
let make_fvar :
  'a .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        FStar_Reflection_Types.term Prims.list ->
          'a vmap ->
            FStar_Tactics_Types.proofstate ->
              ('a polynomial * FStar_Reflection_Types.term Prims.list * 'a
                vmap) FStar_Tactics_Result.__result
  =
  fun t ->
    fun unquotea ->
      fun ts ->
        fun vm ->
          match find t ts with
          | FStar_Pervasives_Native.Some v ->
              (fun s -> FStar_Tactics_Result.Success (((Pvar v), ts, vm), s))
          | FStar_Pervasives_Native.None ->
              (fun ps ->
                 match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1514))
                                        (Prims.of_int (17))
                                        (Prims.of_int (1514))
                                        (Prims.of_int (26))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommSemiring.fst"
                                  (Prims.of_int (1515)) (Prims.of_int (4))
                                  (Prims.of_int (1516)) (Prims.of_int (47)))))
                 with
                 | true ->
                     (match (unquotea t)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommSemiring.fst"
                                                      (Prims.of_int (1514))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (1514))
                                                      (Prims.of_int (26))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1515))
                                                (Prims.of_int (4))
                                                (Prims.of_int (1516))
                                                (Prims.of_int (47))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (1515))
                                          (Prims.of_int (12))
                                          (Prims.of_int (1515))
                                          (Prims.of_int (22))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps') ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1516))
                                            (Prims.of_int (4))
                                            (Prims.of_int (1516))
                                            (Prims.of_int (47)))))
                           with
                           | true ->
                               FStar_Tactics_Result.Success
                                 (((Pvar (FStar_List_Tot_Base.length ts)),
                                    (FStar_List_Tot_Base.op_At ts [t]),
                                    (update (FStar_List_Tot_Base.length ts)
                                       a1 vm)),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1516))
                                               (Prims.of_int (4))
                                               (Prims.of_int (1516))
                                               (Prims.of_int (47))))))))
                      | FStar_Tactics_Result.Failed (e, ps') ->
                          FStar_Tactics_Result.Failed (e, ps')))
let rec reification_aux :
  'a .
    (FStar_Reflection_Types.term ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      FStar_Reflection_Types.term Prims.list ->
        'a vmap ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term ->
                    FStar_Tactics_Types.proofstate ->
                      ('a polynomial * FStar_Reflection_Types.term Prims.list
                        * 'a vmap) FStar_Tactics_Result.__result
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun add ->
          fun opp ->
            fun mone ->
              fun mult ->
                fun t ->
                  fun ps ->
                    match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1521))
                                           (Prims.of_int (15))
                                           (Prims.of_int (1521))
                                           (Prims.of_int (32))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1521)) (Prims.of_int (2))
                                     (Prims.of_int (1543))
                                     (Prims.of_int (38)))))
                    with
                    | true ->
                        ((match FStar_Reflection_Derived_Lemmas.collect_app_ref
                                  t
                          with
                          | (hd, tl) ->
                              (fun ps1 ->
                                 match match (FStar_Tactics_Builtins.inspect
                                                hd)
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (1522))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (1522))
                                                                 (Prims.of_int (33))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1522))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (1522))
                                                           (Prims.of_int (18))))))
                                       with
                                       | FStar_Tactics_Result.Success
                                           (a1, ps') ->
                                           (match FStar_Tactics_Types.tracepoint
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1522))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (1522))
                                                             (Prims.of_int (33)))))
                                            with
                                            | true ->
                                                FStar_Tactics_Result.Success
                                                  ((a1,
                                                     (FStar_List_Tot_Base.list_unref
                                                        tl)),
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (1522))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (1522))
                                                                (Prims.of_int (33))))))))
                                       | FStar_Tactics_Result.Failed 
                                           (e, ps') ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps')
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1522))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (1543))
                                                       (Prims.of_int (38)))))
                                      with
                                      | true ->
                                          ((match a1 with
                                            | (FStar_Reflection_Data.Tv_FVar
                                               fv,
                                               (t1, uu___)::(t2, uu___1)::[])
                                                ->
                                                (fun ps2 ->
                                                   match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1530))
                                                                    (Prims.of_int (24))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30)))))
                                                   with
                                                   | true ->
                                                       (match match (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1530))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (34))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a2, ps'1)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (38)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_eq
                                                                    a2 add),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (38))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30)))))
                                                             with
                                                             | true ->
                                                                 (if a2
                                                                  then
                                                                    (
                                                                    fun ps3
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm add
                                                                    opp mone
                                                                    mult t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (76))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a3
                                                                    with
                                                                    | (e1,
                                                                    ts1, vm1)
                                                                    ->
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1
                                                                    add opp
                                                                    mone mult
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (76))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a4
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    vm2) ->
                                                                    ((Pplus
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (21))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (21)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                                  else
                                                                    (
                                                                    fun ps3
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (39)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_eq
                                                                    a3 mult),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (39))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (if a3
                                                                    then
                                                                    (fun ps4
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm add
                                                                    opp mone
                                                                    mult t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (76))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (e1,
                                                                    ts1, vm1)
                                                                    ->
                                                                    (fun ps5
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1
                                                                    add opp
                                                                    mone mult
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (76))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (21)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a5
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    vm2) ->
                                                                    ((Pmult
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1529))
                                                                    (Prims.of_int (21))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1528))
                                                                    (Prims.of_int (21)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                                    else
                                                                    make_fvar
                                                                    t
                                                                    unquotea
                                                                    ts vm)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1533))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30)))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1532))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1534))
                                                                    (Prims.of_int (30)))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)))
                                            | (FStar_Reflection_Data.Tv_FVar
                                               fv, (t1, uu___)::[]) ->
                                                (fun ps2 ->
                                                   match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1538))
                                                                    (Prims.of_int (20))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1541))
                                                                    (Prims.of_int (30)))))
                                                   with
                                                   | true ->
                                                       (match match (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1538))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1541))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (34))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a2, ps'1)
                                                                  ->
                                                                  (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (38)))))
                                                                   with
                                                                   | 
                                                                   true ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Builtins.term_eq
                                                                    a2 opp),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (38))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e, ps'1)
                                                                  ->
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1541))
                                                                    (Prims.of_int (30)))))
                                                             with
                                                             | true ->
                                                                 (if a2
                                                                  then
                                                                    (
                                                                    fun ps3
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm add
                                                                    opp mone
                                                                    mult t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (75))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (20)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a3
                                                                    with
                                                                    | 
                                                                    (e, ts1,
                                                                    vm1) ->
                                                                    ((Popp e),
                                                                    ts1, vm1))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1537))
                                                                    (Prims.of_int (20))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                                  else
                                                                    make_fvar
                                                                    t
                                                                    unquotea
                                                                    ts vm)
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1540))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1541))
                                                                    (Prims.of_int (30)))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e, ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)))
                                            | (FStar_Reflection_Data.Tv_Const
                                               uu___, []) ->
                                                (fun ps2 ->
                                                   match match (unquotea t)
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (41))))))
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a2, ps'1) ->
                                                             (match FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (41)))))
                                                              with
                                                              | true ->
                                                                  FStar_Tactics_Result.Success
                                                                    ((Pconst
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (41))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (49)))))
                                                        with
                                                        | true ->
                                                            FStar_Tactics_Result.Success
                                                              ((a2, ts, vm),
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1542))
                                                                    (Prims.of_int (49))))))))
                                                   | FStar_Tactics_Result.Failed
                                                       (e, ps'1) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'1))
                                            | (uu___, uu___1) ->
                                                make_fvar t unquotea ts vm))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1522))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (1543))
                                                        (Prims.of_int (38)))))))
                                 | FStar_Tactics_Result.Failed (e, ps') ->
                                     FStar_Tactics_Result.Failed (e, ps'))))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1521))
                                            (Prims.of_int (15))
                                            (Prims.of_int (1521))
                                            (Prims.of_int (32))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1521))
                                      (Prims.of_int (2))
                                      (Prims.of_int (1543))
                                      (Prims.of_int (38))))))
let (steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.iota;
  FStar_Pervasives.zeta;
  FStar_Pervasives.delta_attr ["FStar.Tactics.CanonCommSemiring.canon_attr"];
  FStar_Pervasives.delta_only
    ["FStar.Mul.op_Star";
    "FStar.Algebra.CommMonoid.int_plus_cm";
    "FStar.Algebra.CommMonoid.int_multiply_cm";
    "FStar.Algebra.CommMonoid.__proj__CM__item__mult";
    "FStar.Algebra.CommMonoid.__proj__CM__item__unit";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_add";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__opp";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_mult";
    "FStar.List.Tot.Base.assoc";
    "FStar.Pervasives.Native.fst";
    "FStar.Pervasives.Native.snd";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
    "FStar.List.Tot.Base.op_At";
    "FStar.List.Tot.Base.append"]]
let (canon_norm :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  = fun uu___ -> FStar_Tactics_Builtins.norm steps
let reification :
  'a .
    (FStar_Reflection_Types.term ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           FStar_Reflection_Types.term FStar_Tactics_Result.__result)
        ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                'a ->
                  FStar_Reflection_Types.term Prims.list ->
                    FStar_Tactics_Types.proofstate ->
                      ('a polynomial Prims.list * 'a vmap)
                        FStar_Tactics_Result.__result
  =
  fun unquotea ->
    fun quotea ->
      fun tadd ->
        fun topp ->
          fun tmone ->
            fun tmult ->
              fun munit ->
                fun ts ->
                  fun ps ->
                    match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1581))
                                           (Prims.of_int (13))
                                           (Prims.of_int (1581))
                                           (Prims.of_int (17))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1582)) (Prims.of_int (2))
                                     (Prims.of_int (1593))
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
                                                      ps
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1581))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (1581))
                                                            (Prims.of_int (17))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommSemiring.fst"
                                                      (Prims.of_int (1582))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (1593))
                                                      (Prims.of_int (31))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1582))
                                                (Prims.of_int (13))
                                                (Prims.of_int (1582))
                                                (Prims.of_int (17))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (1583))
                                          (Prims.of_int (2))
                                          (Prims.of_int (1593))
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
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (17))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (1582))
                                                                 (Prims.of_int (13))
                                                                 (Prims.of_int (1582))
                                                                 (Prims.of_int (17))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1583))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (1593))
                                                           (Prims.of_int (31))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (1583))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (1583))
                                                     (Prims.of_int (18))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1584))
                                               (Prims.of_int (2))
                                               (Prims.of_int (1593))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (18))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (1584))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (1593))
                                                                (Prims.of_int (31))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1584))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (1584))
                                                          (Prims.of_int (18))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1585))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (1593))
                                                    (Prims.of_int (31)))))
                                   with
                                   | true ->
                                       (match (FStar_Tactics_Util.map
                                                 (FStar_Tactics_Derived.norm_term
                                                    steps) ts)
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1581))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1582))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1583))
                                                                    (Prims.of_int (18))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1584))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1584))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1584))
                                                                    (Prims.of_int (18))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (1585))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (1593))
                                                                  (Prims.of_int (31))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1585))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (1585))
                                                            (Prims.of_int (48))))))
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a1, ps') ->
                                            (match FStar_Tactics_Types.tracepoint
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1587))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (1593))
                                                              (Prims.of_int (31)))))
                                             with
                                             | true ->
                                                 (match (FStar_Tactics_Util.fold_left
                                                           (fun uu___ ->
                                                              fun t ->
                                                                match uu___
                                                                with
                                                                | (es, vs,
                                                                   vm) ->
                                                                    (
                                                                    fun ps1
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    vs vm
                                                                    tadd topp
                                                                    tmone
                                                                    tmult t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (76))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,
                                                                    ps'1) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (22)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a2
                                                                    with
                                                                    | 
                                                                    (e, vs1,
                                                                    vm1) ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1590))
                                                                    (Prims.of_int (22))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)))
                                                           ([], [],
                                                             ([], munit)) a1)
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1587))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1588))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1592))
                                                                    (Prims.of_int (29))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a2, ps'1) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1587))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31)))))
                                                       with
                                                       | true ->
                                                           FStar_Tactics_Result.Success
                                                             (((match a2 with
                                                                | (es, uu___,
                                                                   vm) ->
                                                                    ((FStar_List_Tot_Base.rev
                                                                    es), vm))),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1587))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1593))
                                                                    (Prims.of_int (31))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e, ps'1) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e, ps'1)))
                                        | FStar_Tactics_Result.Failed
                                            (e, ps') ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps')))))
let rec quote_polynomial :
  'a .
    FStar_Reflection_Types.term ->
      ('a ->
         FStar_Tactics_Types.proofstate ->
           FStar_Reflection_Types.term FStar_Tactics_Result.__result)
        ->
        'a polynomial ->
          FStar_Tactics_Types.proofstate ->
            FStar_Reflection_Types.term FStar_Tactics_Result.__result
  =
  fun ta ->
    fun quotea ->
      fun e ->
        match e with
        | Pconst c ->
            (fun ps ->
               match match match match (quotea c)
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
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1598))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (1598))
                                                                    (Prims.of_int (75))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (1598))
                                                                 (Prims.of_int (33))
                                                                 (Prims.of_int (1598))
                                                                 (Prims.of_int (75))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1598))
                                                           (Prims.of_int (52))
                                                           (Prims.of_int (1598))
                                                           (Prims.of_int (74))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (1598))
                                                     (Prims.of_int (53))
                                                     (Prims.of_int (1598))
                                                     (Prims.of_int (61))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1, ps') ->
                                     (match FStar_Tactics_Types.tracepoint
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1598))
                                                       (Prims.of_int (52))
                                                       (Prims.of_int (1598))
                                                       (Prims.of_int (74)))))
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
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1598))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (1598))
                                                          (Prims.of_int (74))))))))
                                 | FStar_Tactics_Result.Failed (e1, ps') ->
                                     FStar_Tactics_Result.Failed (e1, ps')
                           with
                           | FStar_Tactics_Result.Success (a1, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1598))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (1598))
                                                 (Prims.of_int (75)))))
                                with
                                | true ->
                                    FStar_Tactics_Result.Success
                                      ([a1],
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1598))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (1598))
                                                    (Prims.of_int (75))))))))
                           | FStar_Tactics_Result.Failed (e1, ps') ->
                               FStar_Tactics_Result.Failed (e1, ps')
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1598))
                                           (Prims.of_int (33))
                                           (Prims.of_int (1598))
                                           (Prims.of_int (75)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                (((ta, FStar_Reflection_Data.Q_Implicit) ::
                                  a1),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1598))
                                              (Prims.of_int (33))
                                              (Prims.of_int (1598))
                                              (Prims.of_int (75))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1598))
                                     (Prims.of_int (16))
                                     (Prims.of_int (1598))
                                     (Prims.of_int (75)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "CanonCommSemiring";
                                       "Pconst"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1598))
                                        (Prims.of_int (16))
                                        (Prims.of_int (1598))
                                        (Prims.of_int (75))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
        | Pvar x ->
            (fun ps ->
               match match (FStar_Tactics_Builtins.pack
                              (FStar_Reflection_Data.Tv_Const
                                 (FStar_Reflection_Data.C_Int x)))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1599))
                                               (Prims.of_int (31))
                                               (Prims.of_int (1599))
                                               (Prims.of_int (58))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (1599))
                                         (Prims.of_int (32))
                                         (Prims.of_int (1599))
                                         (Prims.of_int (57))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1599))
                                           (Prims.of_int (31))
                                           (Prims.of_int (1599))
                                           (Prims.of_int (58)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ([a1],
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1599))
                                              (Prims.of_int (31))
                                              (Prims.of_int (1599))
                                              (Prims.of_int (58))))))))
                     | FStar_Tactics_Result.Failed (e1, ps') ->
                         FStar_Tactics_Result.Failed (e1, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1599))
                                     (Prims.of_int (14))
                                     (Prims.of_int (1599))
                                     (Prims.of_int (58)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_e_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "CanonCommSemiring";
                                       "Pvar"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1599))
                                        (Prims.of_int (14))
                                        (Prims.of_int (1599))
                                        (Prims.of_int (58))))))))
               | FStar_Tactics_Result.Failed (e1, ps') ->
                   FStar_Tactics_Result.Failed (e1, ps'))
        | Pplus (e1, e2) ->
            (fun ps ->
               match match (quote_polynomial ta quotea e1)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1601))
                                               (Prims.of_int (22))
                                               (Prims.of_int (1601))
                                               (Prims.of_int (84))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (1601))
                                         (Prims.of_int (23))
                                         (Prims.of_int (1601))
                                         (Prims.of_int (52))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1601))
                                           (Prims.of_int (22))
                                           (Prims.of_int (1601))
                                           (Prims.of_int (84)))))
                          with
                          | true ->
                              (match match (quote_polynomial ta quotea e2)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (84))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (1601))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (1601))
                                                               (Prims.of_int (84))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommSemiring.fst"
                                                         (Prims.of_int (1601))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (1601))
                                                         (Prims.of_int (83))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a2, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1601))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (1601))
                                                           (Prims.of_int (84)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ([a2],
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1601))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (1601))
                                                              (Prims.of_int (84))))))))
                                     | FStar_Tactics_Result.Failed (e3, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e3, ps'1)
                               with
                               | FStar_Tactics_Result.Success (a2, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (1601))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (1601))
                                                     (Prims.of_int (84)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((a1 :: a2),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1601))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (1601))
                                                        (Prims.of_int (84))))))))
                               | FStar_Tactics_Result.Failed (e3, ps'1) ->
                                   FStar_Tactics_Result.Failed (e3, ps'1)))
                     | FStar_Tactics_Result.Failed (e3, ps') ->
                         FStar_Tactics_Result.Failed (e3, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1601)) (Prims.of_int (4))
                                     (Prims.of_int (1601))
                                     (Prims.of_int (84)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_e_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "CanonCommSemiring";
                                       "Pplus"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1601))
                                        (Prims.of_int (4))
                                        (Prims.of_int (1601))
                                        (Prims.of_int (84))))))))
               | FStar_Tactics_Result.Failed (e3, ps') ->
                   FStar_Tactics_Result.Failed (e3, ps'))
        | Pmult (e1, e2) ->
            (fun ps ->
               match match (quote_polynomial ta quotea e1)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1603))
                                               (Prims.of_int (22))
                                               (Prims.of_int (1603))
                                               (Prims.of_int (84))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (1603))
                                         (Prims.of_int (23))
                                         (Prims.of_int (1603))
                                         (Prims.of_int (52))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1603))
                                           (Prims.of_int (22))
                                           (Prims.of_int (1603))
                                           (Prims.of_int (84)))))
                          with
                          | true ->
                              (match match (quote_polynomial ta quotea e2)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1603))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1603))
                                                                    (Prims.of_int (84))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (1603))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (1603))
                                                               (Prims.of_int (84))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommSemiring.fst"
                                                         (Prims.of_int (1603))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (1603))
                                                         (Prims.of_int (83))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a2, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1603))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (1603))
                                                           (Prims.of_int (84)))))
                                          with
                                          | true ->
                                              FStar_Tactics_Result.Success
                                                ([a2],
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1603))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (1603))
                                                              (Prims.of_int (84))))))))
                                     | FStar_Tactics_Result.Failed (e3, ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e3, ps'1)
                               with
                               | FStar_Tactics_Result.Success (a2, ps'1) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (1603))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (1603))
                                                     (Prims.of_int (84)))))
                                    with
                                    | true ->
                                        FStar_Tactics_Result.Success
                                          ((a1 :: a2),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1603))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (1603))
                                                        (Prims.of_int (84))))))))
                               | FStar_Tactics_Result.Failed (e3, ps'1) ->
                                   FStar_Tactics_Result.Failed (e3, ps'1)))
                     | FStar_Tactics_Result.Failed (e3, ps') ->
                         FStar_Tactics_Result.Failed (e3, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1603)) (Prims.of_int (4))
                                     (Prims.of_int (1603))
                                     (Prims.of_int (84)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_e_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "CanonCommSemiring";
                                       "Pmult"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1603))
                                        (Prims.of_int (4))
                                        (Prims.of_int (1603))
                                        (Prims.of_int (84))))))))
               | FStar_Tactics_Result.Failed (e3, ps') ->
                   FStar_Tactics_Result.Failed (e3, ps'))
        | Popp e1 ->
            (fun ps ->
               match match (quote_polynomial ta quotea e1)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1604))
                                               (Prims.of_int (31))
                                               (Prims.of_int (1604))
                                               (Prims.of_int (61))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (1604))
                                         (Prims.of_int (32))
                                         (Prims.of_int (1604))
                                         (Prims.of_int (60))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps') ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1604))
                                           (Prims.of_int (31))
                                           (Prims.of_int (1604))
                                           (Prims.of_int (61)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ([a1],
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1604))
                                              (Prims.of_int (31))
                                              (Prims.of_int (1604))
                                              (Prims.of_int (61))))))))
                     | FStar_Tactics_Result.Failed (e2, ps') ->
                         FStar_Tactics_Result.Failed (e2, ps')
               with
               | FStar_Tactics_Result.Success (a1, ps') ->
                   (match FStar_Tactics_Types.tracepoint
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1604))
                                     (Prims.of_int (14))
                                     (Prims.of_int (1604))
                                     (Prims.of_int (61)))))
                    with
                    | true ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_e_app
                              (FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "CanonCommSemiring";
                                       "Popp"]))) a1),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1604))
                                        (Prims.of_int (14))
                                        (Prims.of_int (1604))
                                        (Prims.of_int (61))))))))
               | FStar_Tactics_Result.Failed (e2, ps') ->
                   FStar_Tactics_Result.Failed (e2, ps'))

let canon_semiring_aux :
  'a .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
        ->
        ('a ->
           FStar_Tactics_Types.proofstate ->
             FStar_Reflection_Types.term FStar_Tactics_Result.__result)
          ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  FStar_Reflection_Types.term ->
                    'a ->
                      FStar_Tactics_Types.proofstate ->
                        unit FStar_Tactics_Result.__result
  =
  fun ta ->
    fun unquotea ->
      fun quotea ->
        fun tr ->
          fun tadd ->
            fun topp ->
              fun tmone ->
                fun tmult ->
                  fun munit ->
                    FStar_Tactics_Derived.focus
                      (fun uu___ ->
                         fun ps ->
                           match (FStar_Tactics_Builtins.norm [])
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1626))
                                               (Prims.of_int (2))
                                               (Prims.of_int (1626))
                                               (Prims.of_int (9))))))
                           with
                           | FStar_Tactics_Result.Success (a1, ps') ->
                               (match FStar_Tactics_Types.tracepoint
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1627))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (1671))
                                                 (Prims.of_int (42)))))
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
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (1627))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (1671))
                                                               (Prims.of_int (42))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommSemiring.fst"
                                                         (Prims.of_int (1627))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (1627))
                                                         (Prims.of_int (21))))))
                                     with
                                     | FStar_Tactics_Result.Success
                                         (a2, ps'1) ->
                                         (match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1628))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (1671))
                                                           (Prims.of_int (42)))))
                                          with
                                          | true ->
                                              (match (FStar_Reflection_Formula.term_as_formula
                                                        a2)
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1628))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (42))))))
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                                   (Prims.of_int (1628))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (1628))
                                                                   (Prims.of_int (25))))))
                                               with
                                               | FStar_Tactics_Result.Success
                                                   (a3, ps'2) ->
                                                   (match FStar_Tactics_Types.tracepoint
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1628))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (42)))))
                                                    with
                                                    | true ->
                                                        ((match a3 with
                                                          | FStar_Reflection_Formula.Comp
                                                              (FStar_Reflection_Formula.Eq
                                                               (FStar_Pervasives_Native.Some
                                                               t), t1, t2)
                                                              ->
                                                              if
                                                                FStar_Reflection_Builtins.term_eq
                                                                  t ta
                                                              then
                                                                (fun ps1 ->
                                                                   match 
                                                                    (reification
                                                                    unquotea
                                                                    quotea
                                                                    tadd topp
                                                                    tmone
                                                                    tmult
                                                                    munit
                                                                    [t1; t2])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1634))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (1634))
                                                                    (Prims.of_int (76))))))
                                                                   with
                                                                   | 
                                                                   FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    ps'3) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1634))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1667))
                                                                    (Prims.of_int (30)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    ((match a4
                                                                    with
                                                                    | (e1::e2::[],
                                                                    vm) ->
                                                                    (fun ps2
                                                                    ->
                                                                    match 
                                                                    (quote_vm
                                                                    ta quotea
                                                                    vm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1648))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1648))
                                                                    (Prims.of_int (39))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (quote_polynomial
                                                                    ta quotea
                                                                    e1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (47))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1651))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (quote_polynomial
                                                                    ta quotea
                                                                    e2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1651))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1651))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1651))
                                                                    (Prims.of_int (47))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1653))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.mapply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
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
                                                                    "CanonCommSemiring";
                                                                    "semiring_reflect"]))),
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (tr,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a5,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a6,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a7,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (t1,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (t2,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1653))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1653))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1654))
                                                                    (Prims.of_int (64))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (21))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1658))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.later
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1658))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1658))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1658))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1660))
                                                                    (Prims.of_int (21))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1662))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.trefl
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1662))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1662))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1662))
                                                                    (Prims.of_int (16))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1664))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (match 
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1664))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1664))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1664))
                                                                    (Prims.of_int (21))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,
                                                                    ps'12) ->
                                                                    (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))
                                                                    with
                                                                    | 
                                                                    true ->
                                                                    (FStar_Tactics_Derived.trefl
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1666))
                                                                    (Prims.of_int (16)))))))
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
                                                                    (e, ps'4))
                                                                    | uu___1
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1634))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1667))
                                                                    (Prims.of_int (30)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                              else
                                                                FStar_Tactics_Derived.fail
                                                                  "Found equality, but terms do not have the expected type"
                                                          | uu___1 ->
                                                              FStar_Tactics_Derived.fail
                                                                "Goal should be an equality"))
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1628))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (42)))))))
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
let canon_semiring :
  'a .
    'a cr ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun r ->
    fun ps ->
      match FStar_Tactics_Types.tracepoint
              (FStar_Tactics_Types.set_proofstate_range
                 (FStar_Tactics_Types.incr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1675)) (Prims.of_int (4))
                             (Prims.of_int (1675)) (Prims.of_int (13))))))
                 (FStar_Range.prims_to_fstar_range
                    (Prims.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                       (Prims.of_int (1674)) (Prims.of_int (2))
                       (Prims.of_int (1680)) (Prims.of_int (17)))))
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
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1675))
                                              (Prims.of_int (4))
                                              (Prims.of_int (1675))
                                              (Prims.of_int (13))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1674))
                                        (Prims.of_int (2))
                                        (Prims.of_int (1680))
                                        (Prims.of_int (17))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommSemiring.fst"
                                  (Prims.of_int (1675)) (Prims.of_int (50))
                                  (Prims.of_int (1675)) (Prims.of_int (59))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommSemiring.fst"
                            (Prims.of_int (1674)) (Prims.of_int (2))
                            (Prims.of_int (1680)) (Prims.of_int (17)))))
           with
           | true ->
               (match match FStar_Tactics_Types.tracepoint
                              (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (13))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (1675))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (1675))
                                                               (Prims.of_int (59))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommSemiring.fst"
                                                         (Prims.of_int (1674))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (1680))
                                                         (Prims.of_int (17))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                   (Prims.of_int (1676))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (1676))
                                                   (Prims.of_int (43))))))
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommSemiring.fst"
                                             (Prims.of_int (1676))
                                             (Prims.of_int (21))
                                             (Prims.of_int (1676))
                                             (Prims.of_int (42))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1676))
                                       (Prims.of_int (4))
                                       (Prims.of_int (1676))
                                       (Prims.of_int (43)))))
                      with
                      | true ->
                          (FStar_Tactics_Derived.norm_term steps
                             (Obj.magic
                                (failwith
                                   "Cannot evaluate open quotation at runtime")))
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (13))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (1675))
                                                                (Prims.of_int (50))
                                                                (Prims.of_int (1675))
                                                                (Prims.of_int (59))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1674))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (1680))
                                                          (Prims.of_int (17))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1676))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (1676))
                                                    (Prims.of_int (43))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1676))
                                              (Prims.of_int (21))
                                              (Prims.of_int (1676))
                                              (Prims.of_int (42))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1676))
                                        (Prims.of_int (4))
                                        (Prims.of_int (1676))
                                        (Prims.of_int (43))))))
                with
                | FStar_Tactics_Result.Success (a1, ps') ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1674))
                                      (Prims.of_int (2))
                                      (Prims.of_int (1680))
                                      (Prims.of_int (17)))))
                     with
                     | true ->
                         (match match FStar_Tactics_Types.tracepoint
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
                                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                                   (Prims.of_int (1674))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (1680))
                                                                   (Prims.of_int (17))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1677))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (1677))
                                                             (Prims.of_int (35))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1677))
                                                       (Prims.of_int (21))
                                                       (Prims.of_int (1677))
                                                       (Prims.of_int (34))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1677))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (1677))
                                                 (Prims.of_int (35)))))
                                with
                                | true ->
                                    (FStar_Tactics_Derived.norm_term steps
                                       (Obj.magic
                                          (failwith
                                             "Cannot evaluate open quotation at runtime")))
                                      (FStar_Tactics_Types.decr_depth
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1677))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (1677))
                                                              (Prims.of_int (35))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1677))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (1677))
                                                        (Prims.of_int (34))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (1677))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (1677))
                                                  (Prims.of_int (35))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1674))
                                                (Prims.of_int (2))
                                                (Prims.of_int (1680))
                                                (Prims.of_int (17)))))
                               with
                               | true ->
                                   (match match FStar_Tactics_Types.tracepoint
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (52))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (1678))
                                                                 (Prims.of_int (21))
                                                                 (Prims.of_int (1678))
                                                                 (Prims.of_int (51))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1678))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (1678))
                                                           (Prims.of_int (52)))))
                                          with
                                          | true ->
                                              (FStar_Tactics_Derived.norm_term
                                                 steps
                                                 (Obj.magic
                                                    (failwith
                                                       "Cannot evaluate open quotation at runtime")))
                                                (FStar_Tactics_Types.decr_depth
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (52))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (1678))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (1678))
                                                                  (Prims.of_int (51))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1678))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (1678))
                                                            (Prims.of_int (52))))))
                                    with
                                    | FStar_Tactics_Result.Success (a3, ps'2)
                                        ->
                                        (match FStar_Tactics_Types.tracepoint
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'2
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1674))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (1680))
                                                          (Prims.of_int (17)))))
                                         with
                                         | true ->
                                             (match match FStar_Tactics_Types.tracepoint
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (43))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (44)))))
                                                    with
                                                    | true ->
                                                        (FStar_Tactics_Derived.norm_term
                                                           steps
                                                           (Obj.magic
                                                              (failwith
                                                                 "Cannot evaluate open quotation at runtime")))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (44))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (43))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1679))
                                                                    (Prims.of_int (44))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a4, ps'3) ->
                                                  (match FStar_Tactics_Types.tracepoint
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'3
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17)))))
                                                   with
                                                   | true ->
                                                       (canon_semiring_aux
                                                          (Obj.magic
                                                             (failwith
                                                                "Cannot evaluate open quotation at runtime"))
                                                          FStar_Tactics_Builtins.unquote
                                                          (fun x ->
                                                             fun s ->
                                                               FStar_Tactics_Result.Success
                                                                 ((Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime")),
                                                                   s))
                                                          (Obj.magic
                                                             (failwith
                                                                "Cannot evaluate open quotation at runtime"))
                                                          a1 a2 a3 a4
                                                          (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                             (__proj__CR__item__cm_add
                                                                r)))
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'3
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1674))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (17)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e, ps'3) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'3)))
                                    | FStar_Tactics_Result.Failed (e, ps'2)
                                        ->
                                        FStar_Tactics_Result.Failed (e, ps'2)))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
let (int_cr : Prims.int cr) =
  CR
    (FStar_Algebra_CommMonoid.int_plus_cm,
      FStar_Algebra_CommMonoid.int_multiply_cm, (~-), (), (), ())

let (int_semiring :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match (FStar_Tactics_Derived.cur_goal ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1693))
                                      (Prims.of_int (10))
                                      (Prims.of_int (1693))
                                      (Prims.of_int (39))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommSemiring.fst"
                                (Prims.of_int (1693)) (Prims.of_int (26))
                                (Prims.of_int (1693)) (Prims.of_int (39))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommSemiring.fst"
                                  (Prims.of_int (1693)) (Prims.of_int (10))
                                  (Prims.of_int (1693)) (Prims.of_int (39)))))
                 with
                 | true ->
                     (FStar_Reflection_Formula.term_as_formula a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommSemiring.fst"
                                   (Prims.of_int (1693)) (Prims.of_int (10))
                                   (Prims.of_int (1693)) (Prims.of_int (39)))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range
                            "FStar.Tactics.CanonCommSemiring.fst"
                            (Prims.of_int (1693)) (Prims.of_int (4))
                            (Prims.of_int (1699)) (Prims.of_int (29)))))
           with
           | true ->
               ((match a with
                 | FStar_Reflection_Formula.Comp
                     (FStar_Reflection_Formula.Eq
                      (FStar_Pervasives_Native.Some t), uu___1, uu___2)
                     ->
                     if
                       FStar_Reflection_Builtins.term_eq t
                         (FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_FVar
                               (FStar_Reflection_Builtins.pack_fv
                                  ["Prims"; "nat"])))
                     then
                       (fun ps1 ->
                          match (FStar_Tactics_Derived.apply_lemma
                                   (FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_FVar
                                         (FStar_Reflection_Builtins.pack_fv
                                            ["FStar";
                                            "Tactics";
                                            "CanonCommSemiring";
                                            "eq_nat_via_int"]))))
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1696))
                                              (Prims.of_int (14))
                                              (Prims.of_int (1696))
                                              (Prims.of_int (43))))))
                          with
                          | FStar_Tactics_Result.Success (a1, ps'1) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1696))
                                                (Prims.of_int (45))
                                                (Prims.of_int (1696))
                                                (Prims.of_int (66)))))
                               with
                               | true ->
                                   (canon_semiring int_cr)
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1696))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (1696))
                                                 (Prims.of_int (66)))))))
                          | FStar_Tactics_Result.Failed (e, ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1))
                     else canon_semiring int_cr
                 | uu___1 -> canon_semiring int_cr))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1693)) (Prims.of_int (4))
                             (Prims.of_int (1699)) (Prims.of_int (29)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
