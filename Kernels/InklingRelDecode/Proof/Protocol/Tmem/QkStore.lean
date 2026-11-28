-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkStoreRound
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A QK MMA and a probability store of one buffer are ordered.** -/
theorem qk_store_order (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) : QkStoreOrder L X := by
  intro x y pc d a s acc mask vals sh hx qk hy cta hd
  obtain ⟨_, _, _, _, _, h⟩ := qk_store_round hp hX hf safe base rows init hx qk hy cta hd
  exact h.imp (·.2) (·.2)

end PTX.Kernels.InklingRelDecode.Proof.Tmem
