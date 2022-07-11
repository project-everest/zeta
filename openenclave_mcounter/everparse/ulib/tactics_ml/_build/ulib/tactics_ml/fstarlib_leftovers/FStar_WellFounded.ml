open Prims
type ('a, 'r, 'x) acc =
  | AccIntro of ('a -> 'r -> ('a, 'r, unit) acc) 
let uu___is_AccIntro : 'a 'r . 'a -> ('a, 'r, unit) acc -> Prims.bool =
  fun x -> fun projectee -> true
let __proj__AccIntro__item___0 :
  'a 'r . 'a -> ('a, 'r, unit) acc -> 'a -> 'r -> ('a, 'r, unit) acc =
  fun x -> fun projectee -> match projectee with | AccIntro _0 -> _0
type ('a, 'r) well_founded = 'a -> ('a, 'r, unit) acc
let acc_inv :
  'aa 'r . 'aa -> ('aa, 'r, unit) acc -> 'aa -> 'r -> ('aa, 'r, unit) acc =
  fun x -> fun a -> match a with | AccIntro h1 -> h1
let rec fix_F :
  'aa 'r 'p .
    ('aa -> ('aa -> 'r -> 'p) -> 'p) -> 'aa -> ('aa, 'r, unit) acc -> 'p
  =
  fun f ->
    fun x -> fun a -> f x (fun y -> fun h -> fix_F f y (acc_inv x a y h))
let fix :
  'aa 'r .
    ('aa, 'r) well_founded ->
      unit -> ('aa -> ('aa -> 'r -> Obj.t) -> Obj.t) -> 'aa -> Obj.t
  = fun rwf -> fun p -> fun f -> fun x -> fix_F f x (rwf x)


type ('a, 'rel) is_well_founded = unit
type 'a well_founded_relation = unit
type ('a, 'rel, 'f, 'uuuuu, 'uuuuu1) as_well_founded = 'rel
let subrelation_wf :
  'a 'r 'subur .
    ('a -> 'a -> 'subur -> 'r) ->
      ('a, 'r) well_founded -> ('a, 'subur) well_founded
  =
  fun sub_w ->
    fun r_wf ->
      let rec aux x acc_r =
        AccIntro
          (fun y ->
             fun sub_r_y_x ->
               aux y
                 (match acc_r with | AccIntro f -> f y (sub_w y x sub_r_y_x))) in
      fun x -> aux x (r_wf x)

type ('a, 'r, 'subur, 'subuw, 'ruwf, 'uuuuu, 'uuuuu1) subrelation_as_wf =
  'subur
type ('a, 'b, 'rub, 'f, 'x, 'y) inverse_image = 'rub
let inverse_image_wf :
  'a 'b 'rub .
    ('a -> 'b) ->
      ('b, 'rub) well_founded ->
        ('a, ('a, 'b, 'rub, unit, unit, unit) inverse_image) well_founded
  =
  fun f ->
    fun r_b_wf ->
      let rec aux x acc_r_b =
        let get_acc_r_b_y y p = match acc_r_b with | AccIntro g -> g (f y) p in
        AccIntro (fun y -> fun p -> aux y (get_acc_r_b_y y p)) in
      fun x -> aux x (r_b_wf (f x))