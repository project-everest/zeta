open Prims
let uncurry : 'a 'b 'c . ('a -> 'b -> 'c) -> ('a * 'b) -> 'c =
  fun f -> fun uu___ -> match uu___ with | (x, y) -> f x y
let curry : 'a 'b 'c . (('a * 'b) -> 'c) -> 'a -> 'b -> 'c =
  fun f -> fun x -> fun y -> f (x, y)
let rec list_ref : 'a 'p . 'a Prims.list -> 'a Prims.list =
  fun l -> match l with | [] -> [] | x::xs -> x :: (list_ref xs)




let (collect_app_ref :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  =
  fun t ->
    let uu___ = FStar_Reflection_Derived.collect_app t in
    match uu___ with | (h, a) -> (h, (list_ref a))