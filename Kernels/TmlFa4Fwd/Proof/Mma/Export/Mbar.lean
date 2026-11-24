-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitTarget
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's mbarrier uses

`mma_mbar_use`: every event of a lane of warp 12 that names an mbarrier and is no initialization is
a poll of a Q, K/V or P barrier, with the parity of the lane's successful polls of it, or a commit
by a lane that won an election. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- The barriers the MMA warp polls. -/
def MmaPollOff (o : Nat) : Prop :=
  o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40 ∨ o = 48 ∨ o = 96 ∨ o = 104 ∨ o = 112 ∨ o = 120
/-- The barriers the MMA warp's commits complete. -/
def MmaCommitOff (o : Nat) : Prop :=
  o = 16 ∨ o = 24 ∨ o = 56 ∨ o = 64 ∨ o = 72 ∨ o = 80 ∨ o = 88 ∨ o = 144 ∨ o = 152

private theorem pollO_off (r : Nat) (s : Mma.Site) (hs : Progress.isPoll s = true) :
    MmaPollOff (Progress.pollO r s) := by
  have h3 : ∀ n, MmaPollOff (32 + 8 * (n % 3)) := by
    intro n
    unfold MmaPollOff
    omega
  cases s <;> simp only [Progress.isPoll, Bool.false_eq_true] at hs
  case wt j => fin_cases j <;> first | exact h3 _ | simp [Progress.pollO, MmaPollOff]
  case mw b ld => simp only [Progress.pollO, MmaPollOff]; split <;> simp

private theorem cmO_off (r : Nat) (c : Fin 12) : MmaCommitOff (Mma.cmO r c) := by
  fin_cases c <;> simp only [Mma.cmO, MmaCommitOff] <;> simp <;> omega

/-- **Every mbarrier use of an MMA lane.** -/
theorem mma_mbar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 12) (he : X.get (h, k) = some e)
    (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ o ok, MmaPollOff o ∧ l = obj L h o ∧
        e.kind = .wait l (okPolls l ((X.tr h).take k) % 2) ok true .cta) ∨
      ∃ o s, MmaCommitOff o ∧ l = obj L h o ∧ e.kind = .tc (.commit s) ∧ s.mbar = l ∧
        s.group = .one ∧
        ∃ j pc' inst, j < k ∧ X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  rcases mma_counts hp hX hFw hw he hub with ⟨s, _, -, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, -, hev⟩
  · exact absurd (start_mbar hev hx hm) (fun ⟨c, hc⟩ => hni c hc)
  · exfalso
    obtain ⟨pc, kind⟩ := e
    rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> simp only at hk <;>
      subst hk <;> simp only [MbarOf] at hm
  cases mma_use hev hm with
  | poll ok hs hl hk =>
    obtain ⟨hl', hq⟩ := Progress.par_eq hp hQ hs
    refine .inl ⟨_, ok, pollO_off r _ hs, hl.trans hl', ?_⟩
    have hpm : Progress.pollPar L d = Progress.pollPar L d % 2 := by
      unfold Progress.pollPar
      split <;> simp
    rw [hk, hpm, hq, hl, hl', mma_okPolls, count hσ]
  | commit c s hs hk hb =>
    have hw : w = true := hcm (by rw [hs]; fin_cases c <;> decide)
    have hwon : 0 < n (.mma .won) := by
      have h1 := hQ.won
      simp only [hw, ite_true] at h1
      change n (.mma .won) = _ at h1
      rw [h1, hs]
      fin_cases c <;> simp [Mma.electAll, Mma.pq, Mma.Site.ord]
    obtain ⟨j, hj, ⟨pc', kd⟩, hf, hcl⟩ := exists_of_count hσ hwon
    cases kd <;> simp [cls, Mma.cls] at hcl
    obtain ⟨rfl, rfl⟩ := hcl
    have hgrp : s.group = .one := by
      obtain ⟨site, v⟩ := d
      simp only at hs
      subst hs
      simp only [Mma.Ev] at hev
      rcases hev with ⟨s', hk', -, hg⟩ | ⟨f, hk'⟩
      · rw [hk] at hk'; cases hk'; exact hg
      · exact absurd hk' (hub f)
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    obtain ⟨rank, ht⟩ := hm
    have hl := commit_target hp hX he ht
    have hmb : s.mbar = obj L h (Mma.cmO r c) :=
      hb.trans (Mma.cm_loc hp c (r := r) (fun hc' => hQ.regs (by
        rw [hs]; fin_cases c <;> simp_all [Mma.Site.ord])))
    have hl' : l = obj L h (Mma.cmO r c) := by rw [hl, hmb]
    exact .inr ⟨_, s, cmO_off r c, hl', rfl, hmb.trans hl'.symm, hgrp, j, pc', _, hj, hf⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
