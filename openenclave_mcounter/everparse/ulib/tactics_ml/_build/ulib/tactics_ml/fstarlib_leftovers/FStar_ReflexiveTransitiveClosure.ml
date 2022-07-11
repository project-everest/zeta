open Prims
type ('a, 'r, 'dummyV0, 'dummyV1) _closure =
  | Refl of 'a 
  | Step of 'a * 'a * 'r 
  | Closure of 'a * 'a * 'a * ('a, 'r, unit, unit) _closure * ('a, 'r, 
  unit, unit) _closure 
let uu___is_Refl :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> Prims.bool =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Refl x -> true | uu___2 -> false
let __proj__Refl__item__x :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 -> fun projectee -> match projectee with | Refl x -> x
let uu___is_Step :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> Prims.bool =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Step (x, y, _2) -> true | uu___2 -> false
let __proj__Step__item__x :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Step (x, y, _2) -> x
let __proj__Step__item__y :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Step (x, y, _2) -> y
let __proj__Step__item___2 :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'r =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Step (x, y, _2) -> _2
let uu___is_Closure :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> Prims.bool =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Closure (x, y, z, _3, _4) -> true
        | uu___2 -> false
let __proj__Closure__item__x :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Closure (x, y, z, _3, _4) -> x
let __proj__Closure__item__y :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Closure (x, y, z, _3, _4) -> y
let __proj__Closure__item__z :
  'a 'r . 'a -> 'a -> ('a, 'r, unit, unit) _closure -> 'a =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Closure (x, y, z, _3, _4) -> z
let __proj__Closure__item___3 :
  'a 'r .
    'a ->
      'a -> ('a, 'r, unit, unit) _closure -> ('a, 'r, unit, unit) _closure
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Closure (x, y, z, _3, _4) -> _3
let __proj__Closure__item___4 :
  'a 'r .
    'a ->
      'a -> ('a, 'r, unit, unit) _closure -> ('a, 'r, unit, unit) _closure
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Closure (x, y, z, _3, _4) -> _4
type ('a, 'r, 'x, 'y) _closure0 = unit



type ('a, 'r, 'uuuuu, 'uuuuu1) closure = unit

let rec closure_one_aux :
  'a 'r .
    'a ->
      'a ->
        ('a, 'r, unit, unit) _closure ->
          (unit,
            ('a, 'r, ('a, 'r, unit, unit) _closure) FStar_Pervasives.dtuple3)
            FStar_Pervasives.either
  =
  fun x ->
    fun y ->
      fun xy ->
        match xy with
        | Refl uu___ -> FStar_Pervasives.Inl ()
        | Step (uu___, uu___1, pr) ->
            FStar_Pervasives.Inr
              (FStar_Pervasives.Mkdtuple3 (y, pr, (Refl y)))
        | Closure (x1, a1, y1, xa, ay) ->
            (match closure_one_aux a1 y1 ay with
             | FStar_Pervasives.Inl uu___ -> closure_one_aux x1 y1 xa
             | FStar_Pervasives.Inr (FStar_Pervasives.Mkdtuple3
                 (z, r_a_z, c_z_y)) ->
                 (match closure_one_aux x1 a1 xa with
                  | FStar_Pervasives.Inl uu___ ->
                      FStar_Pervasives.Inr
                        (FStar_Pervasives.Mkdtuple3 (z, r_a_z, c_z_y))
                  | FStar_Pervasives.Inr (FStar_Pervasives.Mkdtuple3
                      (w, r_x_w, c_w_a)) ->
                      let c_w_y =
                        let c_a_y =
                          Closure (a1, z, y1, (Step (a1, z, r_a_z)), c_z_y) in
                        Closure (w, a1, y1, c_w_a, c_a_y) in
                      FStar_Pervasives.Inr
                        (FStar_Pervasives.Mkdtuple3 (w, r_x_w, c_w_y))))






