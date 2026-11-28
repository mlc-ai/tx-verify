-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Top.Safe.LateOWord
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Lib.WinSet
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaDecl
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleDecl
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Export.SumDecl
import Kernels.InklingRelDecode.Proof.Softmax.Export.SumWord
import Kernels.InklingRelDecode.Proof.Softmax.Export.ScaleDecl

@[expose] public section

/-! # The arithmetic of the softmax and the epilogue is not declined

The pieces of `Iface.LateValues.noDecline`, by group of pcs: the scale multiplication of pc 601
and the rescale multiplications of pcs 2262 to 2325. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The scale multiplication of pc 601 is not declined.** -/
theorem Safe.declScale (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ g t, Iface.LaneState L X g t → t.pc = 601 →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none :=
  fun _ _ hl hpc _ hc => Softmax.Export.scale_decl hp hX hl hpc hc

/-- **The rescale multiplications of pcs 2262 to 2325 are not declined.** -/
theorem Safe.declRescale (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → 2262 ≤ t.pc → t.pc ≤ 2325 →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro g t lane hl h1 h2 i hc
  exact Softmax.Export.rescale_decl hp hX hf (hS g)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf (hS) lane g1)
    (fun k a vals sh he x hx => by
      obtain ⟨r, rfl⟩ := Safe.ldOFloat hp hX hf hou safe rows init nub he (Or.inl rfl) x hx
      exact Flow.has_float_fl r)
    lane hl h1 h2 hc

/-- **The rescale difference and products of pcs 1842, 1843 and 1848 are not declined.** -/
theorem Safe.declAlpha (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → 1839 ≤ t.pc → t.pc ≤ 1848 →
      (t.pc = 1842 ∨ t.pc = 1843 ∨ t.pc = 1848) →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro g t _ hl h1 h2 h3 i hc
  exact Softmax.Export.alpha_decl hp hX hf (hS g)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf (hS) lane g1)
    hl h1 h2 h3 hc

/-- **The sums of the exponentials, their halves and the row sum (pcs 2201 to 2235) are not
declined.** -/
theorem Safe.declSum (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → 2201 ≤ t.pc → t.pc ≤ 2235 →
      Iface.declinePc t.pc = true →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  have h5 : ∀ {g}, g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv :=
    fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf hS lane g1
  intro g t lane hl h1 h2 hd i hc
  by_cases h3 : t.pc ≤ 2233
  · have hdo : Iface.declineOp i.op = true := by
      simp only [Iface.declinePc, hc, Bool.and_eq_true] at hd
      exact hd.2
    exact Softmax.Export.sum_decl hp hX hf (hS g) (h5 (g := g)) hl h1 h3 hc hdo
  · have h4 : t.pc = 2235 := by
      have : t.pc ≠ 2234 := fun h => by
        rw [h] at hd
        exact absurd hd (by decide +kernel)
      omega
    refine Softmax.Export.sum_add_decl hp hX hf (hS g) (h5 (g := g)) ?_ hl h4 hc
    intro k mode sent b c recv ok get
    obtain ⟨rfl, rfl, rfl, -⟩ := Softmax.Export.sent_sum hp hX hf (hS g) (h5 (g := g)) get
    obtain ⟨j, b', c', r', o', got, low, -⟩ :=
      Softmax.Export.late_partner hp hX hf get (by omega) (by omega) lane
    obtain ⟨-, -, -, hs⟩ := Softmax.Export.sent_sum hp hX hf (hS _) (h5 (g := _)) got
    exact hs

private theorem declinePc_scan : Lib.scanCode (fun pc ins =>
    !(((decide (574 ≤ pc) && decide (pc < 2331)) || (decide (2560 ≤ pc) && decide (pc < 2853))) &&
      !Assumptions.emuSites.contains pc && Iface.declineOp ins.op) ||
      decide (pc = 601 ∨ pc = 1842 ∨ pc = 1843 ∨ pc = 1848 ∨ (2201 ≤ pc ∧ pc ≤ 2235) ∨
        (2262 ≤ pc ∧ pc ≤ 2325) ∨ (2642 ≤ pc ∧ pc ≤ 2673))) kernel.code 0 = true := by
  decide +kernel

/-- The pcs of the arithmetic without a rounding modifier are in these groups. -/
theorem declinePc_range (pc : Nat) (h : Iface.declinePc pc = true) :
    pc = 601 ∨ pc = 1842 ∨ pc = 1843 ∨ pc = 1848 ∨ (2201 ≤ pc ∧ pc ≤ 2235) ∨
      (2262 ≤ pc ∧ pc ≤ 2325) ∨ (2642 ≤ pc ∧ pc ≤ 2673) := by
  cases hc : kernel.code[pc]? with
  | none => simp [Iface.declinePc, hc] at h
  | some ins =>
    have := Lib.scanCode_get declinePc_scan hc
    simp only [Iface.declinePc, hc] at h
    rw [Nat.zero_add] at this
    simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this

/-- **The ideal-real rule does not decline `add`, `sub` and `mul`** (`noDecline`), from the
groups of pcs, the last (the epilogue's products) given. -/
theorem Safe.noDeclineOf (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (epi : ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → 2642 ≤ t.pc → t.pc ≤ 2673 →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → Iface.declinePc t.pc = true →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none := by
  intro g t lane hl hd i hc
  rcases declinePc_range _ hd with h | h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Safe.declScale hp hX g t hl h i hc
  · exact Safe.declAlpha hp hX hf hou safe rows init nub g t lane hl (by omega) (by omega)
      (.inl h) i hc
  · exact Safe.declAlpha hp hX hf hou safe rows init nub g t lane hl (by omega) (by omega)
      (.inr (.inl h)) i hc
  · exact Safe.declAlpha hp hX hf hou safe rows init nub g t lane hl (by omega) (by omega)
      (.inr (.inr h)) i hc
  · exact Safe.declSum hp hX hf hou safe rows init nub g t lane hl h1 h2 hd i hc
  · exact Safe.declRescale hp hX hf hou safe rows init nub g t lane hl h1 h2 i hc
  · exact epi g t lane hl h1 h2 i hc

end PTX.Kernels.InklingRelDecode.Proof.Top
