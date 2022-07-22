module Zeta.TimeKey

let lt_is_total (tk1 tk2: timestamp_key)
  : Lemma (ensures (tk1 = tk2 /\ ~ (tk1 `lt` tk2) /\ ~ (tk2 `lt` tk1) \/
                    tk1 <> tk2 /\ (tk1 `lt` tk2 \/ tk2 `lt` tk1)))
  = Zeta.BinTree.lt_is_total (snd tk1) (snd tk2)

let lt_is_transitive (tk1 tk2 tk3: _)
  : Lemma (ensures (tk1 `lt` tk2 ==> tk2 `lt` tk3 ==> tk1 `lt` tk3))
  = Zeta.BinTree.lt_is_transitive (snd tk1) (snd tk2) (snd tk3)
