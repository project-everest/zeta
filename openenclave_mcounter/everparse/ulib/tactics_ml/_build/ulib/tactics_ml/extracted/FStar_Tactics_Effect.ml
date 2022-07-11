open Prims
type 'a __tac =
  FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
let __ret : 'a . 'a -> 'a __tac =
  fun x -> fun s -> FStar_Tactics_Result.Success (x, s)
let __bind :
  'a 'b .
    Prims.range -> Prims.range -> 'a __tac -> ('a -> 'b __tac) -> 'b __tac
  =
  fun r1 ->
    fun r2 ->
      fun t1 ->
        fun t2 ->
          fun ps ->
            let ps1 =
              FStar_Tactics_Types.set_proofstate_range ps
                (FStar_Range.prims_to_fstar_range r1) in
            let ps2 = FStar_Tactics_Types.incr_depth ps1 in
            let r = t1 ps2 in
            match r with
            | FStar_Tactics_Result.Success (a1, ps') ->
                let ps'1 =
                  FStar_Tactics_Types.set_proofstate_range ps'
                    (FStar_Range.prims_to_fstar_range r2) in
                (match FStar_Tactics_Types.tracepoint ps'1 with
                 | true -> t2 a1 (FStar_Tactics_Types.decr_depth ps'1))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
let (__get : unit -> FStar_Tactics_Types.proofstate __tac) =
  fun uu___ -> fun s0 -> FStar_Tactics_Result.Success (s0, s0)
let __raise : 'a . Prims.exn -> 'a __tac =
  fun e -> fun ps -> FStar_Tactics_Result.Failed (e, ps)
type 'a __tac_wp = unit
type ('a, 'b, 'wp, 'f, 'ps, 'post) g_bind = 'wp
type ('a, 'wp, 'ps, 'post) g_compact = unit
type ('a, 'b, 'wp, 'f, 'uuuuu, 'uuuuu1) __TAC_eff_override_bind_wp = unit
type ('a, 'wp, 's, 'pu) _dm4f_TAC_lift_from_pure = 'wp
type ('a, 'x, 's, 'pu) _dm4f_TAC_return_wp = 'pu
let _dm4f_TAC_return_elab :
  'a .
    'a -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun x -> fun s -> FStar_Tactics_Result.Success (x, s)
let _dm4f_TAC_bind_elab :
  'a 'b .
    Prims.range ->
      Prims.range ->
        unit ->
          (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
            ->
            unit ->
              ('a ->
                 FStar_Tactics_Types.proofstate ->
                   'b FStar_Tactics_Result.__result)
                ->
                FStar_Tactics_Types.proofstate ->
                  'b FStar_Tactics_Result.__result
  =
  fun r1 ->
    fun r2 ->
      fun t1__w ->
        fun t1 ->
          fun t2__w ->
            fun t2 ->
              fun ps ->
                let ps1 =
                  FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range r1) in
                let ps2 = FStar_Tactics_Types.incr_depth ps1 in
                let r = t1 ps2 in
                match r with
                | FStar_Tactics_Result.Success (a1, ps') ->
                    let ps'1 =
                      FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range r2) in
                    (match FStar_Tactics_Types.tracepoint ps'1 with
                     | true -> t2 a1 (FStar_Tactics_Types.decr_depth ps'1))
                | FStar_Tactics_Result.Failed (e, ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
let _dm4f_TAC___proj__TAC__item____raise_elab :
  'a .
    Prims.exn ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun e -> fun ps -> FStar_Tactics_Result.Failed (e, ps)
type _dm4f_TAC___proj__TAC__item____raise_complete_type =
  unit ->
    Prims.exn ->
      FStar_Tactics_Types.proofstate -> Obj.t FStar_Tactics_Result.__result
let (_dm4f_TAC___proj__TAC__item____get_elab :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.proofstate FStar_Tactics_Result.__result)
  = fun uu___ -> fun s0 -> FStar_Tactics_Result.Success (s0, s0)
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.proofstate FStar_Tactics_Result.__result
type ('a, 'wpua) _dm4f_TAC_repr =
  FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
type _dm4f_TAC_pre = unit
type 'a _dm4f_TAC_post = unit
type 'a _dm4f_TAC_wp = unit
type ('a, 't) _dm4f_TAC_ctx = FStar_Tactics_Types.proofstate -> unit -> 't
type ('a, 't) _dm4f_TAC_gctx = unit
let _dm4f_TAC_pure :
  'a 't . 't -> FStar_Tactics_Types.proofstate -> unit -> 't =
  fun x -> fun uu___ -> fun uu___1 -> x




type ('a, 'c, 'uuuuu, 'uuuuu1, 'uuuuu2, 'uuuuu3) _dm4f_TAC_wp_if_then_else =
  unit
type ('a, 'b, 'f, 'uuuuu, 'uuuuu1) _dm4f_TAC_wp_close = unit
type ('a, 'wp1, 'wp2) _dm4f_TAC_stronger = unit
type ('a, 'wp, 'uuuuu, 'uuuuu1) _dm4f_TAC_ite_wp = unit
type ('a, 'uuuuu, 'uuuuu1) _dm4f_TAC_null_wp = unit
type ('a, 'wp) _dm4f_TAC_wp_trivial = unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab
let __proj__TAC__item____raise e ps = FStar_Tactics_Result.Failed (e, ps)
let __proj__TAC__item____get uu___1 s0 =
  FStar_Tactics_Result.Success (s0, s0)
type ('a, 'wp, 'ps, 'p) lift_div_tac = 'wp
let (get :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.proofstate FStar_Tactics_Result.__result)
  = __proj__TAC__item____get
let raise :
  'a .
    Prims.exn ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun e -> __proj__TAC__item____raise e
type ('uuuuu, 'p) with_tactic = 'p
let (rewrite_with_tactic :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> unit -> Obj.t -> Obj.t)
  = fun uu___ -> fun uu___1 -> fun p -> p
let synth_by_tactic :
  'uuuuu .
    (unit ->
       FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
      -> 'uuuuu
  = fun uu___ -> Prims.admit ()


let assume_safe :
  'a .
    (unit ->
       FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result)
      -> FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun tau -> tau ()
type ('a, 'b) tac =
  'a -> FStar_Tactics_Types.proofstate -> 'b FStar_Tactics_Result.__result
type 'a tactic = (unit, 'a) tac




