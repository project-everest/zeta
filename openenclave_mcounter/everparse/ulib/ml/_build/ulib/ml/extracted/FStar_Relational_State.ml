open Prims
let read_rel1 :
  'uuuuu . 'uuuuu FStar_ST.ref -> 'uuuuu FStar_Relational_Relational.double =
  fun r ->
    FStar_Relational_Comp.compose2_self FStar_Ref.read
      (FStar_Relational_Relational.twice r)
let read_rel2 :
  'uuuuu .
    unit ->
      'uuuuu FStar_ST.ref FStar_Relational_Relational.double ->
        'uuuuu FStar_Relational_Relational.double
  = fun uu___ -> FStar_Relational_Comp.compose2_self FStar_Ref.read
let assign_rel1 :
  'uuuuu .
    'uuuuu FStar_ST.ref ->
      ('uuuuu, 'uuuuu) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r ->
    fun v ->
      FStar_Relational_Comp.compose2_self
        (fun uu___ -> match uu___ with | (a, b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel
           (FStar_Relational_Relational.twice r) v)
let assign_rel2 :
  'uuuuu .
    ('uuuuu FStar_ST.ref, 'uuuuu FStar_ST.ref)
      FStar_Relational_Relational.rel ->
      ('uuuuu, 'uuuuu) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r ->
    fun v ->
      FStar_Relational_Comp.compose2_self
        (fun uu___ -> match uu___ with | (a, b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel r v)