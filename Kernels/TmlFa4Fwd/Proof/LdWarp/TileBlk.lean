-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileInv
public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileNum
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The tile words of a block state in numbers (`blk_num`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The request of a CTA is one. -/
theorem work_unique {c b b' : Nat} (h1 : tilePrefix p b * p.heads ≤ c)
    (h2 : c < tilePrefix p (b + 1) * p.heads) (h1' : tilePrefix p b' * p.heads ≤ c)
    (h2' : c < tilePrefix p (b' + 1) * p.heads) : b = b' := by
  rcases lt_trichotomy b b' with hlt | hlt | hlt
  · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b + 1 ≤ b' from hlt))
    omega
  · exact hlt
  · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b' + 1 ≤ b from hlt))
    omega

/-- **The tile words of a block state.** -/
theorem blk_num (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv nc : Nat}
    (hb : d.site.blk = true) (hF : LFits p L g d ns nv nc) (hT : TileW p L g d.v) :
    ∃ b, TileNum p L g d.v d.v.su b := by
  obtain ⟨R, bal, hP, hco, hsu, huk⟩ := hT
  obtain ⟨b, hN⟩ := tile_num hp hg hP
  have hFE := (lfits_blk_of hb hF).2.1
  simp only [Epilogue.Fits, toE, epi_blk hb] at hFE
  obtain ⟨R', bal', hC, hc0, hc1⟩ := hFE
  obtain ⟨hPk, -, hgx, -, hbal, -, -, -, -⟩ := id hC
  obtain ⟨rfl, rfl⟩ := hP.unique hPk
  simp only [Epilogue.chosen] at hgx hbal hc0 hc1
  have hch : Epilogue.chosen d.v.sc =
      Epilogue.chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [Epilogue.chosen, hgx, hbal, Epilogue.chosenD]
  refine ⟨b, hN.batch, hN.lo, hN.hi, hch.trans hN.chosen, ?_, ?_, huk.trans hN.ukw,
    by rw [hco]; exact hN.head, by rw [hsu]; exact hN.row, by rw [hsu]; exact hN.r28⟩
  · rw [← hN.c0]
    exact hc0.trans (congrArg (Epilogue.qv p) hch)
  · rw [← hN.c1]
    exact hc1.trans (congrArg (fun z => Epilogue.qv p (addi z 1)) hch)

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
