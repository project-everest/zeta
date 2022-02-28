module Zeta.Steel.Rel

module GK = Zeta.GenKey
module T = Zeta.Steel.FormatsManual

let lift_key (k: s_key)
  : i_key
  = let open T in
    let open GK in
    match k with
    | InternalKey k -> IntK (lift_base_key k)
    | ApplicationKey k -> AppK k

let lower_key (k: i_key)
  : s_key
  = let open T in
    let open GK in
    match k with
    | IntK k -> InternalKey (lower_base_key k)
    | AppK k -> ApplicationKey k

let lemma_lower_lift_key (k: s_key)
  : Lemma (ensures (let open T in
                    let open GK in
                    ApplicationKey? k ==> lower_key (lift_key k) = k))
  = ()

let related_root (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (TSM.is_root_key sk <==> ik = GK.IntK Zeta.BinTree.Root))
  = admit()

let related_root_inv (_:unit)
  : Lemma (ensures (let rk = TSM.root_key in
                    let i_rk = GK.IntK Zeta.BinTree.Root in
                    related_key rk i_rk))
  = admit()


let lemma_related_key_proper_descendent (sk0 sk1: s_base_key) (ik0 ik1: i_base_key)
  : Lemma (requires (related_base_key sk0 ik0 /\ related_base_key sk1 ik1))
          (ensures (is_proper_descendent sk0 sk1 <==> Zeta.BinTree.is_proper_desc ik0 ik1) /\
                   (is_proper_descendent sk0 sk1 ==>
                    (related_desc_dir (desc_dir sk0 sk1) (Zeta.BinTree.desc_dir ik0 ik1))))
  = admit()

let lemma_related_base_key (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (let s = TSM.to_base_key sk in
                    let i = GK.to_base_key ik in
                    related_base_key s i))
  = admit()

let related_app_key (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik /\
                     T.ApplicationKey? sk))
          (ensures (GK.AppK? ik /\
                    (let T.ApplicationKey ak = sk in
                     let GK.AppK i_ak = ik in
                     ak = i_ak)))
  = admit()

let related_zero (_:unit)
  : Lemma (ensures (related_hash_value TSM.zero Zeta.Hash.zero))
  = admit()

let lift_desc_hash (sdh: s_desc_hash)
  : idh: i_desc_hash { related_desc_hash sdh idh }
  = admit()

let lift_mval (smv: s_mval)
  : imv: i_mval { related_mval smv imv }
  = admit()

let lift_dval (sdv: s_dval)
  : idv: i_dval {related_dval sdv idv}
  = admit()

let lift_val (sv: s_val)
  : iv: i_val { related_val sv iv }
  = admit()

let lift_record (sr: s_record {valid_record sr})
  : ir: i_record { related_record sr ir }
  = admit()

let lift_timestamp (st: s_timestamp)
  : i_timestamp
  = admit()

let related_next (st: s_timestamp) (it: i_timestamp)
  : Lemma (requires (related_timestamp st it))
          (ensures (match TSM.next st with
                    | None -> True
                    | Some st' -> related_timestamp st' (Zeta.Time.next it)))
  = admit()

let related_max (st1 st2: s_timestamp) (it1 it2: i_timestamp)
  : Lemma (requires (related_timestamp st1 it1 /\ related_timestamp st2 it2))
          (ensures (related_timestamp (TSM.max st1 st2) (Zeta.Time.max it1 it2)))
  = admit()

let related_timestamp_lt (st1 st2: s_timestamp) (it1 it2: i_timestamp)
  : Lemma (requires (related_timestamp st1 it1 /\ related_timestamp st2 it2))
          (ensures (st1 `TSM.timestamp_lt` st2 <==> it1 `Zeta.Time.ts_lt` it2))
  = admit()

let related_timestamp_zero (_: unit)
  : Lemma (ensures (let st = 0uL in
                    let it = { Zeta.Time.e = 0 ; Zeta.Time.c = 0 } in
                    related_timestamp st it))
  = admit()

let related_timestamp_epoch (st: s_timestamp) (it: i_timestamp)
  : Lemma (requires (related_timestamp st it))
          (ensures (let se = TSM.epoch_of_timestamp st in
                    let ie = it.Zeta.Time.e in
                    related_epoch se ie))
  = admit()

let related_epoch_incr (s: s_epoch) (i: i_epoch)
  : Lemma (requires (related_epoch s i /\ FStar.UInt.fits (U32.v s + 1) 32))
          (ensures (related_epoch (U32.add s U32.one) (i+1)))
  = admit()

let related_epoch_shift (se: s_epoch) (ie: i_epoch)
  : Lemma (ensures (let open Zeta.Time in
                    let st = U64.shift_left (FStar.Int.Cast.uint32_to_uint64 se) 32ul in
                    let it = {e = ie; c = 0} in
                    related_timestamp st it))
  = admit()

let related_hashfn (sv: s_val) (iv: i_val)
  : Lemma (requires (related_val sv iv))
          (ensures (related_hash_value (s_hashfn sv) (i_hashfn iv)))
  = admit()

let related_init_value (sk: s_key) (ik: i_key)
  : Lemma (requires (related_key sk ik))
          (ensures (related_val (TSM.init_value sk) (Zeta.Record.init_value ik)))
  = admit()
