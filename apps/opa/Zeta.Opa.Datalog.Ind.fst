module Zeta.Opa.Datalog.Ind

(* An inductive semantics for datalog. *)

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.List.Tot
open Zeta.Set
open FStar.Ghost

let (@@) l i = List.Tot.index l i

let list_index l = i:nat{i < length l}

(* this is a fold right *)
let rec list_map_reduce #a #b (m : a -> b) (f : b -> b -> b) (z : b) (l : list a) : b =
  match l with
  | [] -> z
  | hd::tl -> m hd `f` list_map_reduce m f z tl

let rec drop #a (i : nat) (l : list a) : list a =
  match i, l with
  | 0, _ -> l
  | _, [] -> []
  | n, x::xs -> drop (n-1) xs

let rec drop_len #a (l : list a) (i : nat{i <= length l})
  : Lemma (length (drop i l) == length l - i)
          [SMTPat (length (drop i l))]
  = match i, l with
    | _, [] -> ()
    | 0, _ -> ()
    | i, x::xs -> drop_len xs (i-1)
  
let rec drop_idx #a (l : list a) (i : nat{i <= length l}) (j : nat)
  : Lemma (requires j < length (drop i l))
          (ensures index (drop i l) j == index l (i+j))
          [SMTPat (index (drop i l) j)]
  = match i, l with
    | _, [] -> ()
    | 0, _ -> ()
    | i, x::xs -> drop_idx xs (i-1) j

let rec drop_tail #a (i : nat) (l : list a)
  : Lemma (drop i (drop 1 l) == drop (i+1) l)
  = match i, l with
    | 0, _ -> ()
    | _, [] -> ()
    | i, hd::tl -> drop_tail (i-1) tl

let rec drop_add #a (i j : nat) (l : list a)
  : Lemma (drop i (drop j l) == drop (i+j) l)
  = if j = 0 then () else
    calc (==) {
      drop i (drop j l);
      == {}
      drop i (drop ((j-1) + 1) l);
      == {drop_tail (j-1) l}
      drop i (drop (j-1) (drop 1 l));
      == {drop_add i (j-1) (drop 1 l)}
      drop (i+j-1) (drop 1 l);
      == {drop_tail (i+j-1) l}
      drop (i+j) l;
    }
  
let rec mapi'_aux #a #b
    (l0 : erased (list a))
    (f  : (idx:(erased (i:nat{i < length l0})) -> v:a{v == List.Tot.index l0 idx} -> b))
    (i  : nat{i <= length l0})
    (l  : list a{l == drop i l0 /\ (i + length l == length l0)})
: Tot (list b) (decreases length l)
= match l with
  | [] -> []
  | x::xs ->
    assert ((x::xs) == drop i l0);
    assert (l == drop i l0);
    drop_add 1 i l0;
    assert (xs == drop (i+1) l0);
    drop_idx l0 i 0;
    assert (x == index l0 i);
    f i x :: mapi'_aux l0 f (i+1) xs

let mapi' #a #b (l0 : list a) (f : (idx:(erased (i:nat{i < length l0})) -> v:a{v == List.Tot.index l0 idx} -> b)) : list b =
  mapi'_aux l0 f 0 l0

let rec mapi_aux_len #a #b
  (l0 : erased (list a)) 
  (f  : (idx:(erased (i:nat{i < length l0})) -> v:a{v == List.Tot.index l0 idx} -> b))
  (i  : nat{i <= length l0})
  (l  : list a{l == drop i l0 /\ (i + length l == length l0)})
: Lemma (ensures length (mapi'_aux l0 f i l) == length l)
        (decreases length l)
= match l with
  | [] -> assert_norm (mapi'_aux l0 f i l == []) // hmm...
  | x::xs ->
    drop_add 1 i l0;
    drop_idx l0 i 0;
    assert_norm (drop 1 (mapi'_aux l0 f i (x::xs)) == mapi'_aux l0 f (i+1) xs);
    mapi_aux_len l0 f (i+1) xs;
    assert_norm (mapi'_aux l0 f i (x::xs) == f i x :: mapi'_aux l0 f (i+1) xs);
    ()

let mapi_len #a #b
  (l : list a)
  (f : (idx:(erased (i:nat{i < length l})) -> v:a{v == List.Tot.index l idx} -> b))
: Lemma (length (mapi' l f) == length l)
= mapi_aux_len l f 0 l

let rec mapi_idx #a #b (l0 : list a) (f : (idx:(erased (i:nat{i < length l0})) -> v:a{v == List.Tot.index l0 idx} -> b))
                       (j : list_index l0)
  : Lemma (ensures (
           let _ = mapi_len l0 f in
           f j (l0 @@ j) == mapi' l0 f @@ j))
          (decreases j)
  = admit ()

#set-options "--warn_error -242" // inner let rec

(* name of a predicate in a datalog query. change to an abstract eqtype?
 * we are also currently using ordering on this domain to avoid recursion
 * datalog rules so it has to be more general than the eqtype ... *)
let name = nat

(* we want to define the semantics of datalog parameterized by: *)
noeq
type param = {
  const_t : eqtype;                        (* type of the constants *)
  total_pred_count: nat;                     (* total pred count *)
  arity: n:name{n < total_pred_count} -> nat; (* predicate arity *)
  // TODO: put the rules in here too?
}

let is_valid_predn (dp: param) (n: name) =
  n < dp.total_pred_count

let pred_name dp : Type = n:nat{n < dp.total_pred_count}

(* a variable in a query. change to an abstract eqtype?  *)
let var_t = nat

(* variable or constant *)
type term (dp: param) =
  | Var: v: var_t -> term dp
  | Const: c: dp.const_t -> term dp

type fvs = set name
class hasFVs (a:Type) = {
  fvs_of : a -> fvs
}

instance hasFVs_unrefine (#a : Type u#aa) (#p : a -> Type u#0) (_ : hasFVs a) : hasFVs (x:a{p x}) = {
  fvs_of = fun (t : (x:a{p x})) -> fvs_of (t <: a)
}

instance fv_term #dp : hasFVs (term dp) = {
  fvs_of = function Var v -> add_elem empty v | Const _ -> empty
}

(* a predicate in a datalog rule. E.g., in "Path (X, Y) : Edge (X, Y)" is constructed
 * from two predicates Path(X,Y) and Edge (X,Y) *)
type pred (dp: param) = {
  n: pred_name dp;
  t: s: list (term dp) { length s == dp.arity n }
}

let is_var (#dp: param) (t: term dp)
  = match t with
    | Var _ -> true
    | _ -> false

let var (#dp: param) (t: term dp { is_var t })
  = match t with
    | Var v -> v

let is_const (#dp: param) (vc: term dp)
  = not (is_var vc)

let const_val (#dp: param) (t: term dp { is_const t })
  : dp.const_t
  = match t with
    | Const c -> c

(* basic structure of a rule *)
type rule_base (dp: param) = {
  head: pred dp;
  body: list (pred dp);
}

instance fv_list #a (_ : hasFVs a) : hasFVs (list a) = {
  fvs_of = list_map_reduce fvs_of union empty
}

let fv_list_nil #a {| _ : hasFVs a |}
  (s : list a)
: Lemma (requires length s == 0)
        (ensures fvs_of s == empty)
= ()

let fv_list_cons #a {| hasFVs a |}
  (hd : a) (tl : list a)
: Lemma (ensures fvs_of (hd::tl) == fvs_of hd `union` fvs_of tl)
        [SMTPat (fvs_of (hd::tl))]
= ()

let rec fv_list_lem #a {| hasFVs a |}
  (s : list a) (i : nat{i < length s})
 : Lemma (ensures fvs_of (s @@ i) `subset` fvs_of s)
         (decreases i)
         [SMTPat (fvs_of (s @@ i))]
 =
 if i > 0 then fv_list_lem (tail s) (i-1)

instance fv_pred  #dp : hasFVs (pred dp) = {
  fvs_of = fun p -> list_map_reduce fvs_of union empty p.t
}

unfold
let var_containment_prop_2 (#dp: param) (r: rule_base dp)
  = fvs_of r.head `subset` fvs_of r.body

(* every variable in the head of a rule occurs in the body *)
// let var_containment_prop (#dp: param) (r: rule_base dp)
//   = // if the i'th pos in the head is a variable then ...
//     forall i. is_var (index r.head.t i)
//     ==>
//     // there exists a body predicate at position j within body predicates s.t.
//     (exists j. (let p = index r.body j in
//            // there exists an index k, such that the k'th term of p is
//            (exists k. let t = index p.t k in
//               // a variable equal to the head variable
//                  is_var t /\ var t = var (index r.head.t i))))

(* the names of all the predicates in the body is "lesser" than the
 * name of the head precluding any recursion *)
let non_recursion_prop (#dp: param) (r: rule_base dp)
  = forall i. let p = index r.body i in
         p.n < r.head.n

let rule_prop (#dp: param) (r: rule_base dp)
  = var_containment_prop_2 r /\
    non_recursion_prop r /\
    r.head.n < dp.total_pred_count
    (* ^ this rule defines a valid predicate. Given the non_recursion_prop
     * this also means every predicate in the body is valid. *)

(* a datalog rule *)
let rule (dp: param) = r: rule_base dp { rule_prop r }

instance fv_rule #dp : hasFVs (rule dp) = {
  fvs_of = fun (r:rule dp) -> fvs_of r.head `union` fvs_of r.body
}

let ruleset dp = list (rule dp)

(* Binding variables to constants. The option is there to allow
for a "partial" (even empty) binding. This is useful when we 
construct the binding while traversing the instances. *)
let var_binding (dp: param) =
  var_t -> option dp.const_t

let set_in_dom #dp (s : set name) (vb : var_binding dp) =
  forall v. v `in_set` s ==> Some? (vb v)

let fv_seq_in_dom_lem #dp #a {| hasFVs a |}
  (s : list a) (vb : var_binding dp)
  : Lemma (requires forall (i:nat). i < length s ==> set_in_dom (fvs_of (s @@ i)) vb)
          (ensures set_in_dom (fvs_of s) vb)
  =
  admit () (* tedious *)

let var_binding_for (dp: param) (#a:Type) {| hasFVs a |} (x:a) =
  vb:(var_binding dp){set_in_dom (fvs_of x) vb}
  //{forall v. v `in_set` fvs_of x ==> Some? (vb v)}

(* A binding such that every variable in ts is indeed bound. *)
let var_binding_for_terms (dp: param) (ts : list (term dp)) =
  //vb:(var_binding dp){forall v. v `in_set` fvs_of ts ==> Some? (vb v)}
  var_binding_for dp ts

let var_binding_for_pred (#dp: param) (p : pred dp) =
  //vb:(var_binding dp){forall v. v `in_set` fvs_of p ==> Some? (vb v)}
  var_binding_for dp p

(* the arity of the head of the predicate *)
let pred_arity (#dp: param) (p: pred dp)
  = assert (length p.t == dp.arity p.n);
    length p.t  // = dp.arity p.n

(* arity of the head predicate of a rule *)
let head_arity (#dp: param) (r: rule dp)
  = let hp = r.head in
    let hn = hp.n in
    dp.arity hn

let subst1 (#dp:param) (t : term dp) (vb : var_binding_for dp t)
  : Tot (dp.const_t)
  = match t with
    | Const c -> c
    | Var v -> Some?.v (vb v)

(* A k-tuple of constants *)
let tuple (dp: param) (k: nat) = s: list dp.const_t { length s = k }

(* substitute all variables in a sequence of terms to get a tuple (of constants) *)
let subst (#dp: param) (s: list (term dp)) (vb: var_binding_for_terms dp s)
  : Tot (tuple dp (length s)) (decreases length s)
  =
  let f1 = (fun (i : erased (i:nat{i < length s})) (t : term dp{t == index s i}) -> match t with
      | Const c -> c
      | Var v ->
        assert (Var v == index s i);
        fv_list_lem s i;
        assert (Some? (vb v));
        Some?.v (vb v)) in
  let r = mapi' s f1 in
  mapi_len s f1;
  r

(* correctness of substitution *)
let lemma_subst (#dp: param) (s: list (term dp)) (vb: var_binding_for_terms dp s) (i: list_index s)
  : Lemma (ensures (let trm = s @@ i in
                    let tup = subst s vb in
                    let ci = tup @@ i in
                    match trm with
                    | Const c -> ci = c
                    | Var v -> 
                      Some ci = vb v))
  = let _ = mapi_idx s (fun (i : erased (i:nat{i < length s})) (t : term dp{t == index s i}) -> match t with
      | Const c -> c
      | Var v ->
        fv_list_lem s i;
        Some?.v (vb v)) i in
    assert (subst s vb @@ i == (match s@@i with | Const c -> c | Var v -> fv_list_lem s i; Some?.v (vb v)));
    ()

(* an instance of a predicate is a set of tuples of the predicates arity *)
let raw_instance (dp: param) (n: pred_name dp) : Type =
  set (tuple dp (dp.arity n))

(* assignment of an instance to every predicate *)
let raw_instance_map (dp: param) = (n: pred_name dp) -> raw_instance dp n

(* a var-binding is satisfiable for a predicate if substituting all the var in
 * terms of the predicate produces a tuple that is in the instance of the predicate *)
let satisfiable (#dp: param) (im: raw_instance_map dp) (p: pred dp) (vb: var_binding_for_pred p)
  = let inst = im p.n in
    let tp = subst p.t vb in
    tp `in_set` inst

//(* can a particular tuple be derived using a given rule? *)
//let derivable_by (#dp: param) (r: rule dp)
//  (im: raw_instance_map dp)
//  (vb: var_binding_for dp r)
//  (t: tuple dp (head_arity r))
//  = t = subst r.head.t vb /\
//    (forall (j : list_index r.body).
//      let _ = assert(set_in_dom (fvs_of (r.body @@ j)) vb) in // FIXME: remove...
//      satisfiable im (index r.body j) vb)
//
//let lem (#dp:param) (vb:var_binding dp) (r:rule dp) (n:nat{n < length r.body})
//  : Lemma (requires set_in_dom (fvs_of r) vb)
//          (ensures set_in_dom (fvs_of (r.body @@ n).t) vb)
//          [SMTPat (set_in_dom (fvs_of (r.body @@ n).t) vb)]
//  = assert (fvs_of r.body `subset` fvs_of r);
//    fv_list_lem r.body n;
//    ()


//rs |- h t1 .. tn
noeq
type proof (#dp:param) (rs : ruleset dp): (h:pred_name dp) -> (t : tuple dp (dp.arity h)) -> Type0 =
  | Pf : #h:_ -> #t:(tuple dp (dp.arity h)) ->
         r:nat{r < length rs} ->
         squash ((rs@@r).head.n == h) ->
         th:(var_binding_for dp (rs@@r)) ->
         sub:(n:nat{n < length (rs@@r).body} ->
                 (let _ = assert (set_in_dom (fvs_of ((rs@@r).body@@n)) th) in // FIXME
                 squash (proof rs (((rs@@r).body@@n).n) (subst ((rs@@r).body@@n).t th)))) ->
         proof rs h t

let provable #dp rs h t = squash (proof #dp rs h t)
  
let p_tuple (dp: param) (n: pred_name dp) (rs : ruleset dp) : Type =
  (tp : tuple dp (dp.arity n) & provable #dp rs n tp)
  
(* an instance of a predicate is a set of tuples of the predicates arity *)
let p_instance (dp: param) (n: pred_name dp) (rs : ruleset dp) : Type =
  set (p_tuple dp n rs)

(* assignment of an instance to every predicate *)
let p_instance_map (dp: param) (rs : ruleset dp) = (n: pred_name dp) -> p_instance dp n rs

let partial_im #dp (rs : ruleset dp) (idx : nat{idx <= dp.total_pred_count}) =
  pim:(p_instance_map dp rs){(forall i. i >= idx ==> pim i == empty)}

let extend #dp (s : var_binding dp) (v : name{s v == None}) (c : dp.const_t) : var_binding dp =
  fun v' -> if v = v' then Some c else s v'

let extends #dp (s1 s2 : var_binding dp) =
  forall v. Some? (s2 v) ==> s1 v == s2 v

let extend_extend #dp (vb1 vb2 : var_binding dp) (n : name{vb2 n == None}) (c : dp.const_t)
  : Lemma (requires vb1 `extends` extend vb2 n c)
          (ensures vb1 `extends` vb2)
  = ()

let (let?) v f = List.Tot.Base.concatMap f v
let return v = [v]
let fail = []

let rec list_unref #a #p1 #p2 (l : list (x:a{p1 x})) : Pure (list (x:a{p2 x})) (requires (forall x. p1 x ==> p2 x)) (ensures fun _ -> True) =
  match l with
  | [] -> []
  | hd::tl -> hd :: list_unref tl

let rec list_ext (#a:Type) (l1 l2 : list a)
  : Lemma (requires length l1 == length l2
                  /\ (forall (i:list_index l1). l1@@i == l2@@i))
          (ensures l1 == l2)
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys ->
      assert (x == l1@@0);
      assert (forall i. xs@@i == l1@@(i+1));
      list_ext xs ys

// substitution is extensional
let subst_ext_lem (dp:param) (p:pred dp) (vb : var_binding_for dp p) (k : tuple dp (dp.arity p.n))
: Lemma (requires (forall (i:nat). i < dp.arity p.n ==> subst1 (p.t@@i) vb == k@@i))
        (ensures subst p.t vb == k)
= assert (length (subst p.t vb) == length k);
  Classical.forall_intro (lemma_subst p.t vb);
  list_ext (subst p.t vb) k;
  ()

let lem_sub_extends #dp (ts : list (term dp)) (vb1 vb2 : var_binding_for dp ts)
  : Lemma (requires vb1 `extends` vb2)
          (ensures subst ts vb1 == subst ts vb2)
  = Classical.forall_intro (lemma_subst ts vb1);
    Classical.forall_intro (lemma_subst ts vb2);
    list_ext (subst ts vb1) (subst ts vb2)

(* Matches a predicate to a tuple, extending a substitution. The result
is always a sub-singleton (no non-determinism here). The resulting
substitution if any) is guaranteed to convert the given predicate into
the tuple. *)
let match1 #dp (s0 : var_binding dp) (p : pred dp) (k : tuple dp (dp.arity p.n))
: Tot (list (vb:var_binding dp{extends vb s0 /\ set_in_dom (fvs_of p) vb /\ subst p.t vb == k }))
=
  let rec aux (i:nat{i <= dp.arity p.n}) (s : var_binding dp{forall j. j < i ==> (set_in_dom (fvs_of (p.t @@ j)) s /\ subst1 (p.t @@ j) s == k@@j)})
  : Tot (list (vb:var_binding dp{extends vb s /\ set_in_dom (fvs_of p) vb /\ subst p.t vb == k }))
        (decreases dp.arity p.n - i)
  =
    if i = dp.arity p.n then begin
      assert (forall (i:nat). i < length p.t ==> set_in_dom (fvs_of (p.t @@ i)) s);
      fv_seq_in_dom_lem p.t s;
      subst_ext_lem dp p s k;
      [s]
    end else
    match (p.t @@ i), k @@ i with
    | Const c1, c2 -> if c1 = c2 then aux (i+1) s else []
    | Var v1, c2 ->
      assert (fvs_of (p.t @@ i) == add_elem empty v1);
      assert (forall a (e e' : a) (s : set a). in_set e' (add_elem s e) <==> (in_set e' s \/ e == e'));
      match s v1 with
      (* Already bound: check for match *)
      | Some c1 ->
        if c1 = c2
        then begin
          // why???
          assert (set_in_dom (fvs_of (p.t @@ i)) s);
          aux (i+1) s
        end
        else []
      (* Unbound: extend *)
      | None -> 
        let s' = extend s v1 c2 in
        extend_extend s' s v1 c2;
        let l : list (vb:var_binding dp {vb `extends` extend s v1 c2 /\ set_in_dom (fvs_of p) vb /\ subst p.t vb == k}) =
          aux (i+1) s'
        in
        // TODO: use a ghost parameter to avoid the extra pass
        list_unref l
  in
  aux 0 s0

let set_choose #a (s : set a) : list a =
  // Cannot define this currently
  admit ()

let ugh (#dp:param) (ps : list (pred dp)) (i : list_index ps) (vb : var_binding_for dp ps) : var_binding_for dp (ps@@i).t =
  fv_list_lem ps i;
  vb

#push-options "--split_queries always"

(*
 Given a rule, and the current set of instances (complete+sounds for all
 the antecedents of this rule), then traverse all possible combinations
 of tuples in the set to generate substitutions that make the
 antecedents provable, and return them.
*)
let rec find_matching_substs_for #dp rs
  (r:nat{r < length rs}) (im : partial_im rs (rs@@r).head.n)
  (ps : list (pred dp)) (s : var_binding dp)
: Tot (list (s2:var_binding_for dp ps{extends s2 s /\ set_in_dom (fvs_of ps) s2 /\
                                      (forall (i:nat). i < length ps ==> provable rs (ps@@i).n (subst (ps@@i).t (ugh ps i s2)))}))
      (decreases length ps)
=
  match ps with
  | [] -> [s]
  | p::ps' ->
    let? (| tp, pf |) = set_choose (im p.n) in
    let? s' = match1 s p tp in
    assert (provable rs p.n tp);
    assert (extends s' s);
    assert (subst p.t s' == tp);
    let r = find_matching_substs_for rs r im ps' s' in
    let? s'' = r in
    assert (extends s'' s');
    lem_sub_extends p.t s'' s';
    assert (subst p.t s'' == tp);
    // we get this from the recursive call, the zero case is explicit above
    assert (forall (i:nat). i < length ps' ==> (let _ = fv_list_lem ps' i in provable rs (ps'@@i).n (subst (ps'@@i).t s'')));
    assert (ps' == tail ps);
    assert (forall (i:nat). i < length ps ==> provable rs (ps@@i).n (subst (ps@@i).t (ugh ps i s'')));
    assert (forall (i:nat). (i > 0 /\ i < length ps) ==> provable rs (ps@@i).n (subst (ps@@i).t (ugh ps i s'')));
    // fun: ^ this weaker (than the previous) assert fails when on its own
    // FIXME: need to write implicit
    return #(s2:var_binding_for dp ps{extends s2 s /\ set_in_dom (fvs_of ps) s2 /\ (forall (i:nat). i < length ps ==>
                                             provable rs (ps@@i).n (subst (ps@@i).t (ugh ps i s2)))})
           s''
#pop-options

#push-options "--split_queries always"

(*
 This takes the substitutions generated by find_matching_substs and applies
 them to the head of the rule, generating the concrete tuples for the rule,
 each with a squashed proof that they are in the semantics.
*)
let compute_tuples_for_rule #dp (rs : ruleset dp)
    (p:name{is_valid_predn dp p}) // the head predicate
    (i : nat{i < length rs}) // rule idx
    (pim : partial_im rs (rs `index` i).head.n) // we have a valid map for every lower pred
: list (p_tuple dp ((rs@@i).head.n) rs)
= let rl : rule dp = rs @@ i in
  let body = rl.body in
  let head = rl.head in
  assert (rule_prop rl);
  assert_norm (forall rl. rule_prop #dp rl ==> var_containment_prop_2 rl); // need norm ??????????
  assert (var_containment_prop_2 (rs @@ i));
  let subst0 = fun v -> None in
  assert (fvs_of head `subset` fvs_of body);
  let ss = find_matching_substs_for rs i pim body subst0 in
  let tuples =
    let? s = ss in
    let h' = subst head.t s in
    assert (set_in_dom (fvs_of body) s);
    assert (set_in_dom (fvs_of body) s);
    assert (forall (i:nat). i < length body ==> provable rs (body@@i).n (subst (body@@i).t s));
    let pf : proof rs head.n h' = Pf i () s (fun n -> 
                 let _ = assert (set_in_dom (fvs_of ((rs@@i).body@@n)) s) in // FIXME: why?
                 // need to extend find_matching_substs to ensure that every substitution
                 // it returns makes the body provable
                 assert (provable rs (body@@n).n (subst (body@@n).t s));
                 ()
    )
    in
    return (| h', Squash.return_squash pf |)
  in
  tuples
#pop-options

let set_from_list (#a:eqtype) (l : list a)
  : set a
  = fold_left add_elem empty l

let add #dp rs (idx:nat{idx < dp.total_pred_count}) (pim : partial_im rs idx) (i : p_instance dp idx rs) : partial_im rs (idx+1) =
  let pim' : p_instance_map dp rs = (fun n -> if n = idx then i else pim n) in
  pim'

(* Compute an instance for predicate `idx` provided every lower predicate
is already saturated in `im` and extend the partial map im. *)
let extend_pim (#dp:param) (rs : ruleset dp) (idx:nat{idx < dp.total_pred_count})
  (pim : partial_im rs idx)
  : partial_im rs (idx+1)
  =
  let rec aux (i:int{-1 <= i /\ i < length rs}) (acc : p_instance dp idx rs) : Tot (p_instance dp idx rs) (decreases i+1) =
    if i = -1 then acc else 
    if (rs `index` i).head.n = idx then
      let here = set_from_list (compute_tuples_for_rule rs idx i pim) in
      let acc = union here acc in
      aux (i-1) acc
    else
      aux (i-1) acc
  in
  let inst = aux (length rs - 1) empty in
  let pim' : p_instance_map dp rs = add rs idx pim inst in
  pim'

(* From a ruleset and an instance map for all the base predicates,
compute an instance map for all predicates. NOTE: No completeness yet,
the result might as well be empty according to the type. *)
let fill (#dp:param) (rs : ruleset dp) : p_instance_map dp rs =
  let im0 : partial_im rs 0 = fun _ -> empty in
  let rec aux (i : nat{i <= dp.total_pred_count}) (pim : partial_im rs i) : Tot (p_instance_map dp rs) (decreases dp.total_pred_count - i) =
    if i = dp.total_pred_count
    then pim
    else aux (i+1) (extend_pim rs i pim)
  in
  aux 0 im0
