module Veritas.BinTreePtr

open Veritas.BinTree

(* pointer based descendant relation *)
noeq type pdesc: ptrfn -> bin_tree_node -> bin_tree_node -> Type = 
  | PSelf: pf: ptrfn -> n:bin_tree_node -> pdesc pf n n
  | PTran: pf: ptrfn -> d:bin_tree_node -> a:bin_tree_node -> _:(pdesc pf d a) -> 
           c:bin_tree_dir{Some? (pf d c)} ->
           pdesc pf (Some?.v (pf d c)) a
