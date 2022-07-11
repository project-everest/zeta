open Prims
type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) lex_t =
  | Left_lex of 'a * 'a * 'b * 'b * 'rua 
  | Right_lex of 'a * 'b * 'b * 'rub 
let uu___is_Left_lex :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Left_lex (x1, x2, y1, y2, _4) -> true
        | uu___2 -> false
let __proj__Left_lex__item__x1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x1
let __proj__Left_lex__item__x2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x2
let __proj__Left_lex__item__y1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y1
let __proj__Left_lex__item__y2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y2
let __proj__Left_lex__item___4 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'rua
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> _4
let uu___is_Right_lex :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Right_lex (x, y1, y2, _3) -> true
        | uu___2 -> false
let __proj__Right_lex__item__x :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> x
let __proj__Right_lex__item__y1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> y1
let __proj__Right_lex__item__y2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> y2
let __proj__Right_lex__item___3 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'rub
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> _3

let rec lex_t_wf_aux :
  'a 'b 'rua 'rub .
    'a ->
      ('a, 'rua, unit) FStar_WellFounded.acc ->
        ('a -> ('b, 'rub) FStar_WellFounded.well_founded) ->
          'b ->
            ('b, 'rub, unit) FStar_WellFounded.acc ->
              ('a, 'b) Prims.dtuple2 ->
                ('a, 'b, 'rua, 'rub, unit, unit) lex_t ->
                  (('a, 'b) Prims.dtuple2,
                    ('a, 'b, 'rua, 'rub, unit, unit) lex_t, unit)
                    FStar_WellFounded.acc
  =
  fun x ->
    fun acc_x ->
      fun wf_b ->
        fun y ->
          fun acc_y ->
            fun t ->
              fun p_t ->
                match p_t with
                | Left_lex (x_t, uu___, y_t, uu___1, p_a) ->
                    FStar_WellFounded.AccIntro
                      (lex_t_wf_aux x_t
                         (match acc_x with
                          | FStar_WellFounded.AccIntro f -> f x_t p_a) wf_b
                         y_t (wf_b x_t y_t))
                | Right_lex (uu___, uu___1, uu___2, uu___3) ->
                    let rec lex_t_wf_aux_y y1 acc_y1 t1 p_t1 =
                      match p_t1 with
                      | Left_lex (x_t, uu___4, y_t, uu___5, p_a) ->
                          FStar_WellFounded.AccIntro
                            (lex_t_wf_aux x_t
                               (match acc_x with
                                | FStar_WellFounded.AccIntro f -> f x_t p_a)
                               wf_b y_t (wf_b x_t y_t))
                      | Right_lex (uu___4, y_t, uu___5, p_b) ->
                          FStar_WellFounded.AccIntro
                            (lex_t_wf_aux_y y_t
                               (match acc_y1 with
                                | FStar_WellFounded.AccIntro f -> f y_t p_b)) in
                    lex_t_wf_aux_y y acc_y t p_t
let lex_t_wf :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu, 'uuuuu2) FStar_WellFounded.well_founded ->
      ('uuuuu -> ('uuuuu1, 'uuuuu3) FStar_WellFounded.well_founded) ->
        (('uuuuu, 'uuuuu1) Prims.dtuple2,
          ('uuuuu, 'uuuuu1, 'uuuuu2, 'uuuuu3, unit, unit) lex_t)
          FStar_WellFounded.well_founded
  =
  fun wf_a ->
    fun wf_b ->
      fun uu___ ->
        match uu___ with
        | Prims.Mkdtuple2 (x, y) ->
            FStar_WellFounded.AccIntro
              (lex_t_wf_aux x (wf_a x) wf_b y (wf_b x y))
type ('a, 'b, 'rua, 'rub, 'uuuuu, 'uuuuu1) lex_aux = Obj.t


type ('a, 'b, 'rua, 'rub, 'wfua, 'wfub, 'uuuuu, 'uuuuu1) lex = Obj.t
let tuple_to_dep_tuple : 'a 'b . ('a * 'b) -> ('a, 'b) Prims.dtuple2 =
  fun x ->
    Prims.Mkdtuple2
      ((FStar_Pervasives_Native.fst x), (FStar_Pervasives_Native.snd x))
type ('a, 'b, 'rua, 'rub, 'x, 'y) lex_t_non_dep =
  ('a, 'b, 'rua, 'rub, unit, unit) lex_t
let lex_t_non_dep_wf :
  'a 'b 'rua 'rub .
    ('a, 'rua) FStar_WellFounded.well_founded ->
      ('b, 'rub) FStar_WellFounded.well_founded ->
        (('a * 'b), ('a, 'b, 'rua, 'rub, unit, unit) lex_t_non_dep)
          FStar_WellFounded.well_founded
  =
  fun wf_a ->
    fun wf_b ->
      let rec get_acc t p =
        let get_acc_aux t1 p_dep =
          match p with
          | FStar_WellFounded.AccIntro f -> f (tuple_to_dep_tuple t1) p_dep in
        FStar_WellFounded.AccIntro
          (fun t1 -> fun p1 -> get_acc t1 (get_acc_aux t1 p1)) in
      fun t ->
        get_acc t (lex_t_wf wf_a (fun uu___ -> wf_b) (tuple_to_dep_tuple t))
type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) sym =
  | Left_sym of 'a * 'a * 'b * 'rua 
  | Right_sym of 'a * 'b * 'b * 'rub 
let uu___is_Left_sym :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Left_sym (x1, x2, y, _3) -> true
        | uu___2 -> false
let __proj__Left_sym__item__x1 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> x1
let __proj__Left_sym__item__x2 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> x2
let __proj__Left_sym__item__y :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> y
let __proj__Left_sym__item___3 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'rua
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> _3
let uu___is_Right_sym :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Right_sym (x, y1, y2, _3) -> true
        | uu___2 -> false
let __proj__Right_sym__item__x :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> x
let __proj__Right_sym__item__y1 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> y1
let __proj__Right_sym__item__y2 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> y2
let __proj__Right_sym__item___3 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'rub
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> _3
let sym_sub_lex :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) ->
        ('a, 'b, 'rua, 'rub, unit, unit) sym ->
          ('a, 'b, 'rua, 'rub, unit, unit) lex_t_non_dep
  =
  fun t1 ->
    fun t2 ->
      fun p ->
        match p with
        | Left_sym (x1, x2, y, p1) -> Left_lex (x1, x2, y, y, p1)
        | Right_sym (x, y1, y2, p1) -> Right_lex (x, y1, y2, p1)
let sym_wf :
  'a 'b 'rua 'rub .
    ('a, 'rua) FStar_WellFounded.well_founded ->
      ('b, 'rub) FStar_WellFounded.well_founded ->
        (('a * 'b), ('a, 'b, 'rua, 'rub, unit, unit) sym)
          FStar_WellFounded.well_founded
  =
  fun wf_a ->
    fun wf_b ->
      FStar_WellFounded.subrelation_wf sym_sub_lex
        (lex_t_non_dep_wf wf_a wf_b)