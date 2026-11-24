-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' mbarrier uses

`corr_mbar_use`: every event of a correction lane that names an mbarrier and is no initialization
is a unit release arrival on a P-full (96, 104), credit (192, 200) or ready (208, 216) barrier, or
a poll of a final O (144, 152) or free (224, 232) barrier, with the parity of the lane's successful
polls of it (plus one on a free barrier). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- A poll of a free barrier is one ahead: its first poll passes on the fresh barrier. -/
def corrΔ (o : Nat) : Nat := if 224 ≤ o then 1 else 0

private theorem poll_tab :
    ∀ st j : Fin 2, (ptsOf (.acquire (Correction.pollOff (.fw st j)))).countP
        (before (.fw st j)) = 0 ∧
      (ptsOf (.acquire (Correction.pollOff (.fw st j)))).countP inRound = 0 ∧
      Correction.pollPar (.fw st j) = corrΔ (Correction.pollOff (.fw st j)) ∧
      Correction.pollOff (.fw st j) < 240 ∧ 144 ≤ Correction.pollOff (.fw st j) := by
  decide

private theorem wend_tab : ∀ b : Bool,
    (ptsOf (.acquire 232)).countP (before (.wend b)) = (if b then 1 else 0) ∧
      (ptsOf (.acquire 232)).countP inRound = 0 := by
  decide

/-- **Every mbarrier use of a correction lane.** -/
theorem corr_mbar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    (he : X.get (h, k) = some e)
    (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ o, (o = 96 ∨ o = 104 ∨ o = 192 ∨ o = 200 ∨ o = 208 ∨ o = 216) ∧ l = obj L h o ∧
        e.kind = .arrive l 0 1 true .cta) ∨
      ∃ o ok, (o = 144 ∨ o = 152 ∨ o = 224 ∨ o = 232) ∧ l = obj L h o ∧
        e.kind = .wait l ((okPolls l ((X.tr h).take k) + corrΔ o) % 2) ok true .cta := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  rcases corr_counts_nonvote hp hX hFw hw hw1 he hub (by
    obtain ⟨pc,kind⟩ := e; rintro pred b rfl; exact hm.elim) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, -, hev, hc⟩
  · exact absurd (start_mbar hev hx hm) (fun ⟨c, hc⟩ => hni c hc)
  rcases corr_mbar2 hev hm with ⟨hk, hl, hmem⟩ | ⟨par, ok, hk, hl, hmem⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    exact .inl ⟨_, by omega, hl, hk⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine .inr ⟨_, ok, by omega, hl, ?_⟩
    obtain ⟨hpar, hs⟩ := corr_poll_par hev hk
    have hl' : l = obj L h (Correction.pollOff d.site) := hl
    have hcn := hQ.cnt (.acquire (Correction.pollOff d.site)) (by simp)
    rw [hk, hpar, hl', corr_okPolls, hc, hcn]
    congr 1
    rcases hs with ⟨st, j, hs⟩ | ⟨b, hs⟩
    · rw [hs]
      obtain ⟨t1, t2, t3, -, -⟩ := poll_tab st j
      rw [passed, t1, t2, t3]
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, corrΔ]
      split <;> rfl
    · rw [hs]
      obtain ⟨t1, t2⟩ := wend_tab b
      show _ = (passed (ptsOf (.acquire 232)) (.wend b) r + corrΔ 232) % 2
      rw [passed, t1, t2, Nat.mul_zero]
      cases b <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Proof
