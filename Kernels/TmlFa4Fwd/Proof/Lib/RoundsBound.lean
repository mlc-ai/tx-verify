-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Progress.Clock
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A tile's rounds are within the time table's slots -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A tile's blocks are at most the bound of the time table's slots.** -/
theorem mma_rounds_bmax (hp : Pre p L m) (hg : g < L.threads) {R : Nat}
    (hR : MmaRounds p L g R) : R + 1 ≤ Progress.bmax p := by
  obtain ⟨r, bal, hP, rfl⟩ := hR
  have hC : Epilogue.ChosenVals p L g r bal (Epilogue.chosenD p (g / L.block) r bal)
      (3 + 7 * (r + 1) + Epilogue.selN bal) 1 := ⟨hP, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨b, hb, -, -, hc, -⟩ := Epilogue.chosen_spec hp hg hC
  have hk := (hp.lengths b hb).2.2
  have hle : p.kLength b ≤ Progress.kMax p :=
    Finset.le_sup (f := p.kLength) (Finset.mem_range.mpr hb)
  have hu : (Loader.refVL p L g r bal).ukw = W (p.kLength b) := by
    show Mma.ukv p (Epilogue.chosen (Epilogue.chosenD p (g / L.block) r bal)) = _
    rw [hc, Mma.ukv]
    have hb2 : b < 2 ^ 31 := by have := hp.shape.2.1; omega
    rw [show Epilogue.r32 (W b) = W b from r32_W (by omega), toNat_W (by omega)]
  have h1 := Loader.r28_le (p := p) (L := L) (g := g) _ hu (by omega)
  have hsv : Loader.sv (Loader.r28Ref p L g r bal) = Mma.Bs p L g (mmaRef p L g r bal) := by
    rw [tile_agree (p := p) rfl r bal]
    show toSigned 32 _ = toSigned 32 (r32 _)
    simp only [toSigned, r32, truncBits, BitVec.toNat_ofNat]
    norm_num [Nat.mod_mod]
    rfl
  change Loader.sv (Loader.r28Ref p L g r bal) ≤ _ at h1
  rw [hsv] at h1
  have := Nat.div_le_div_right (c := 128) hle
  unfold Progress.bmax
  generalize Mma.Bs p L g (mmaRef p L g r bal) = B at h1 ⊢
  push_cast at h1
  omega

end PTX.Kernels.TmlFa4Fwd.Proof
