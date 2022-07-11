open Prims
type ('t, 'dummyV0, 'dummyV1, 'dummyV2) calc_proof =
  | CalcRefl of 't 
  | CalcStep of unit Prims.list * unit * 't * 't * 't * ('t, unit, unit,
  unit) calc_proof * unit 
let uu___is_CalcRefl :
  't .
    unit Prims.list ->
      't -> 't -> ('t, unit, unit, unit) calc_proof -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcRefl x -> true | uu___3 -> false
let __proj__CalcRefl__item__x :
  't . unit Prims.list -> 't -> 't -> ('t, unit, unit, unit) calc_proof -> 't
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 -> fun projectee -> match projectee with | CalcRefl x -> x
let uu___is_CalcStep :
  't .
    unit Prims.list ->
      't -> 't -> ('t, unit, unit, unit) calc_proof -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with
          | CalcStep (rs, p, x, y, z, _5, _6) -> true
          | uu___3 -> false
let __proj__CalcStep__item__rs :
  't .
    unit Prims.list ->
      't -> 't -> ('t, unit, unit, unit) calc_proof -> unit Prims.list
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> rs
let __proj__CalcStep__item__x :
  't . unit Prims.list -> 't -> 't -> ('t, unit, unit, unit) calc_proof -> 't
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> x
let __proj__CalcStep__item__y :
  't . unit Prims.list -> 't -> 't -> ('t, unit, unit, unit) calc_proof -> 't
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> y
let __proj__CalcStep__item__z :
  't . unit Prims.list -> 't -> 't -> ('t, unit, unit, unit) calc_proof -> 't
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> z
let __proj__CalcStep__item___5 :
  't .
    unit Prims.list ->
      't ->
        't ->
          ('t, unit, unit, unit) calc_proof ->
            ('t, unit, unit, unit) calc_proof
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> _5

type ('t, 'x, 'y) calc_pack =
  {
  rels: unit Prims.list ;
  proof: ('t, unit, unit, unit) calc_proof }
let __proj__Mkcalc_pack__item__rels :
  't . 't -> 't -> ('t, unit, unit) calc_pack -> unit Prims.list =
  fun x ->
    fun y -> fun projectee -> match projectee with | { rels; proof;_} -> rels
let __proj__Mkcalc_pack__item__proof :
  't .
    't ->
      't -> ('t, unit, unit) calc_pack -> ('t, unit, unit, unit) calc_proof
  =
  fun x ->
    fun y ->
      fun projectee -> match projectee with | { rels; proof;_} -> proof
let pk_rels : 't . 't -> 't -> ('t, unit, unit) calc_pack -> unit Prims.list
  = fun x -> fun y -> fun pk -> pk.rels
type ('t, 'rs, 'x, 'y) calc_chain_related = Obj.t
type ('t, 'rs, 'p) calc_chain_compatible = unit

let _calc_init : 't . 't -> ('t, unit, unit, unit) calc_proof =
  fun x -> CalcRefl x
let calc_init : 't . 't -> ('t, unit, unit) calc_pack =
  fun x -> { rels = []; proof = (_calc_init x) }



