module Zeta.MultiSetHashDomain

module K = Zeta.Key
module R = Zeta.Record
module M = Zeta.Merkle

let nkey (n:nat) = k:base_key{Zeta.BinTree.depth k = n}

let rec compare_nkey (n:nat)
  : cmp (nkey n)
  = let open Zeta.BinTree in
    let f =
        fun (k1 k2:nkey n) ->
          match k1, k2 with
          | Root, Root -> true
          | LeftChild _, RightChild _ -> true
          | RightChild _, LeftChild _ -> false
          | LeftChild c1, LeftChild c2
          | RightChild c1, RightChild c2  -> compare_nkey (n - 1) c1 c2
    in
    f

let compare_key
  : cmp base_key
  = let f = fun (k1 k2:base_key) ->
        let open Zeta.BinTree in
        if k1 = k2 then true
        else if depth k1 = depth k2 then compare_nkey (depth k1) k1 k2
        else depth k1 <= depth k2
    in
    f

let compare_merkle_key
  : cmp merkle_key
  = let f = fun (k1 k2:merkle_key) ->
        let open Zeta.BinTree in
        if k1 = k2 then true
        else if depth k1 = depth k2 then compare_nkey (depth k1) k1 k2
        else depth k1 <= depth k2
    in
    f

let rec compare_lseq' (#a:eqtype) (f:cmp a) (l:nat) (s1 s2:Seq.lseq a l)
  : Tot bool
  = if l = 0 then (assert (Seq.equal s1 s2); true)
    else if s1 = s2 then true
    else if Seq.head s1 = Seq.head s2 then compare_lseq' f (l - 1) (Seq.tail s1) (Seq.tail s2)
    else f (Seq.head s1) (Seq.head s2)

let rec compare_lseq'_total_order #a (c:cmp a) (l:nat)
  : Lemma (total_order (Seq.lseq a l) (compare_lseq' c l))
  = let f = compare_lseq' c l in
    if l = 0
    then (
      assert (forall (a1 a2: Seq.lseq a l). (f a1 a2 /\ f a2 a1)  ==> a1 `Seq.equal` a2 /\ a1 == a2)  (* anti-symmetry *)
    )
    else (
      let f' = compare_lseq' c (l - 1) in
      let aux (a1 a2:Seq.lseq a l)
        : Lemma
          (requires (Seq.head a1 = Seq.head a2))
          (ensures (f a1 a2 == f' (Seq.tail a1) (Seq.tail a2)))
          [SMTPat (f a1 a2)]
        = ()
      in
      compare_lseq'_total_order c (l - 1);
      assert (total_order _ f');
      let aux (s1 s2:Seq.lseq a l)
        : Lemma
          (requires
            Seq.head s1 == Seq.head s2 /\
            Seq.equal (Seq.tail s1) (Seq.tail s2))
          (ensures
            s1 == s2)
          [SMTPat (Seq.head s1);
           SMTPat (Seq.head s2)]
        =  assert (s1 `Seq.equal` Seq.cons (Seq.head s1) (Seq.tail s1));
           assert (s2 `Seq.equal` Seq.cons (Seq.head s2) (Seq.tail s2));
           assert (Seq.equal s1 s2)
      in
      assert (forall (a1 a2:Seq.lseq a l). (f a1 a2 /\ f a2 a1)  ==> a1 `Seq.equal` a2);   (* anti-symmetry *)
      assert (forall (a1 a2 a3:Seq.lseq a l). f a1 a2 /\ f a2 a3 ==> f a1 a3);    (* transitivity  *)
      assert (forall (a1 a2:Seq.lseq a l). f a1 a2 \/ f a2 a1)                    (* totality      *)
    )

let compare_lseq (#a:eqtype) (f:cmp a) (l:nat)
  : cmp (Seq.lseq a l)
  = compare_lseq'_total_order f l;
    compare_lseq' f l

let compare_seq (#a:eqtype) (f:cmp a)
  : cmp (Seq.seq a)
  = let f = fun (s1 s2:Seq.seq a) ->
        if s1 = s2 then true
        else if Seq.length s1 = Seq.length s2 then compare_lseq f (Seq.length s1) s1 s2
        else Seq.length s1 <= Seq.length s2
    in
    f

let compare_hash_value
  : cmp Zeta.Hash.hash_value
  = let f = fun h1 h2 -> compare_seq (fun b1 b2 -> if b1 = b2 then true else b1) h1 h2 in
    f

let compare_desc_hash
  : cmp M.desc_hash_t
  = let open Zeta.Merkle in
    let f = fun (d1 d2:desc_hash_t) ->
        if d1 = d2 then true
        else match d1, d2 with
             | Empty, _ -> true
             | _, Empty -> false
             | Desc k1 h1 b1, Desc k2 h2 b2 ->
               if k1 = k2
               then if h1 = h2
                    then b1
                    else compare_hash_value h1 h2
               else compare_key k1 k2
    in
    f

let compare_merkle_value
  : cmp M.value
  = let open Zeta.Merkle in
    let f = fun m1 m2 ->
        if m1 = m2 then true
        else if m1.left = m2.left then compare_desc_hash m1.right m2.right
             else compare_desc_hash m1.left m2.left
    in
    f

let compare_gen_key (aprm: app_params)
  : cmp (GenKey.key aprm)
  = let open Zeta.GenKey in
    let f = fun (k1 k2: key aprm) ->
    if k1 = k2 then true
    else match k1, k2 with
         | IntK _, AppK _ -> true
         | AppK _, IntK _ -> false
         | IntK k1, IntK k2 -> compare_merkle_key k1 k2
         | AppK k1, AppK k2 -> aprm.keycmp k1 k2
    in
    f

let compare_gen_value (aprm: app_params)
  : cmp (R.value aprm)
  = let f = fun (v1 v2: R.value aprm) ->
    if v1 = v2 then true
    else match v1, v2 with
         | IntV _, AppV _ -> true
         | AppV _, IntV _ -> false
         | IntV v1, IntV v2 -> compare_merkle_value v1 v2
         | AppV v1, AppV v2 -> aprm.valcmp v1 v2
    in
    f

let compare_record (aprm: app_params)
  : cmp (R.record aprm)
  = let f = fun (r1 r2: R.record aprm) ->
        let k1,v1 = r1 in
        let k2,v2 = r2 in
        if k1 = k2 then compare_gen_value aprm v1 v2
        else compare_gen_key aprm k1 k2
    in
    f

let ms_hashfn_dom_cmp (aprm: app_params)
  : cmp (ms_hashfn_dom aprm)
  = let f = fun m1 m2 ->
      let MHDom r1 t1 i1 = m1 in
      let MHDom r2 t2 i2 = m2 in
      if r1 = r2
      then if t1 = t2
           then i1 <= i2
           else t1 `ts_leq` t2
      else compare_record aprm r1 r2
    in
    f
