module Zeta.MultiSetHashDomain

let nkey (n:nat) = k:key{Zeta.BinTree.depth k = n}

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
  : cmp key
  = let f = fun (k1 k2:key) ->
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
  : cmp desc_hash
  = let f = fun (d1 d2:desc_hash) ->
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
  : cmp merkle_value
  = let f = fun m1 m2 ->
        if m1 = m2 then true
        else let MkValue l1 r1 = m1 in
             let MkValue l2 r2 = m2 in
             if l1 = l2 then compare_desc_hash r1 r2
             else compare_desc_hash l1 l2
    in
    f

let compare_merkle_record
  : cmp merkle_record
  = let f = fun r1 r2 ->
        let k1,v1 = r1 in
        let k2,v2 = r2 in
        if k1 = k2
        then compare_merkle_value v1 v2
        else compare_merkle_key k1 k2
    in
    f

let compare_data_record (aprm: app_params)
  : cmp (app_record aprm.adm)
  = let f = fun (r1 r2: app_record aprm.adm) ->
            let k1,v1 = r1 in
            let k2,v2 = r2 in
            if k1 = k2
            then aprm.valcmp v1 v2
            else aprm.keycmp k1 k2
    in
    f

let compare_record (aprm: app_params)
  : cmp (record aprm)
  = let f = fun (r1 r2: record aprm) ->
        match r1, r2 with
        | App _, Int _ -> false
        | Int _, App _ -> true
        | App r1, App r2 -> compare_data_record aprm r1 r2
        | Int r1, Int r2 -> compare_merkle_record r1 r2
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
