open Prims
type ('a, 'f) total_order = unit
type 'a cmp = 'a -> 'a -> Prims.bool
let rec sorted : 'a . 'a cmp -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | x::[] -> true
      | x::y::tl -> ((f x y) && (x <> y)) && (sorted f (y :: tl))
type ('a, 'f) ordset = 'a Prims.list

let as_list :
  'uuuuu . 'uuuuu cmp -> ('uuuuu, unit) ordset -> 'uuuuu Prims.list =
  fun uu___ -> fun s -> s
let empty : 'uuuuu . 'uuuuu cmp -> ('uuuuu, unit) ordset = fun uu___ -> []
let mem :
  'uuuuu . 'uuuuu cmp -> 'uuuuu -> ('uuuuu, unit) ordset -> Prims.bool =
  fun uu___ -> fun x -> fun s -> FStar_List_Tot_Base.mem x s
let rec insert' :
  'uuuuu .
    'uuuuu cmp -> 'uuuuu -> ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset
  =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> [x]
        | hd::tl ->
            if x = hd
            then hd :: tl
            else if f x hd then x :: hd :: tl else hd :: (insert' f x tl)
let rec union :
  'uuuuu .
    'uuuuu cmp ->
      ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset
  =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | [] -> s2
        | hd::tl -> union uu___ tl (insert' uu___ hd s2)
let rec intersect :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | [] -> []
        | hd::tl ->
            if mem f hd s2
            then insert' f hd (intersect f tl s2)
            else intersect f tl s2
let choose :
  'a . 'a cmp -> ('a, unit) ordset -> 'a FStar_Pervasives_Native.option =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | x::uu___ -> FStar_Pervasives_Native.Some x
let rec remove' : 'a . 'a cmp -> 'a -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> []
        | hd::tl -> if x = hd then tl else hd :: (remove' f x tl)
let remove : 'a . 'a cmp -> 'a -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f -> fun x -> fun s -> remove' f x s
let size : 'a . 'a cmp -> ('a, unit) ordset -> Prims.nat =
  fun f -> fun s -> FStar_List_Tot_Base.length s
let rec subset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f ->
    fun s1 ->
      fun s2 ->
        match (s1, s2) with
        | ([], uu___) -> true
        | (hd::tl, hd'::tl') ->
            if (f hd hd') && (hd = hd')
            then subset f tl tl'
            else
              if (f hd hd') && (Prims.op_Negation (hd = hd'))
              then false
              else subset f s1 tl'
        | (uu___, uu___1) -> false
let singleton : 'a . 'a cmp -> 'a -> ('a, unit) ordset =
  fun f -> fun x -> [x]
let rec remove_le :
  'a . 'a cmp -> 'a -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> []
        | y::ys -> if (f x y) && (x <> y) then s else remove_le f x ys
let rec minus' :
  'a .
    'a cmp ->
      'a -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun x ->
      fun s1 ->
        fun s2 ->
          match s1 with
          | [] -> []
          | x1::xs1 ->
              (match s2 with
               | [] -> s1
               | x2::xs2 ->
                   if x1 = x2
                   then minus' f x xs1 xs2
                   else x1 :: (minus' f x1 xs1 (remove_le f x1 s2)))
let minus :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | [] -> []
        | x1::xs1 -> minus' f x1 xs1 (remove_le f x1 s2)
let strict_subset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> (s1 <> s2) && (subset f s1 s2)
let disjoint :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> (intersect f s1 s2) = (empty f)
type ('a, 'f, 's1, 's2) equal = unit





















let fold :
  'a 'acc .
    'a cmp -> ('acc -> 'a -> 'acc) -> 'acc -> ('a, unit) ordset -> 'acc
  =
  fun f ->
    fun g -> fun init -> fun s -> FStar_List_Tot_Base.fold_left g init s
let rec map_internal :
  'a 'b .
    'a cmp -> 'b cmp -> ('a -> 'b) -> ('a, unit) ordset -> ('b, unit) ordset
  =
  fun fa ->
    fun fb ->
      fun g ->
        fun sa ->
          match sa with
          | [] -> []
          | x::xs ->
              let y = g x in
              let ys = map_internal fa fb g xs in
              if
                (Prims.op_Negation (Prims.uu___is_Cons ys)) ||
                  ((Prims.__proj__Cons__item__hd ys) <> y)
              then y :: ys
              else ys
let map :
  'a 'b .
    'a cmp -> 'b cmp -> ('a -> 'b) -> ('a, unit) ordset -> ('b, unit) ordset
  = fun fa -> fun fb -> fun g -> fun sa -> map_internal fa fb g sa











let rec as_set : 'a . 'a cmp -> ('a, unit) ordset -> 'a FStar_Set.set =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Set.empty ()
      | hd::tl -> FStar_Set.union (FStar_Set.singleton hd) (as_set f tl)

