-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The round and the time of the MMA warp at a P poll -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A poll of a P barrier: its place, its stage and half, and its successful polls. -/
theorem p_poll_place {r : Nat} {s : Mma.Site} (hs : Progress.isPoll s = true)
    (ho : 96 ≤ Progress.pollO r s) (hr : s.ord < 20 → r = 0) :
    20 ≤ s.ord ∧ s.ord < 86 ∧ Mma.acqAt s.ord r (Progress.pollO r s) = r ∧
      ∃ st : Fin 2, Progress.pollO r s = 96 + 8 * st.val ∨
        Progress.pollO r s = 112 + 8 * st.val := by
  have hm : (2 * r + 1) % 3 < 3 ∧ (2 * r + 2) % 3 < 3 := by omega
  cases s <;> simp only [Progress.isPoll, Bool.false_eq_true] at hs
  case wt k =>
    revert ho
    fin_cases k <;> simp only [Progress.pollO, Mma.Site.ord, List.getD_cons_succ,
      List.getD_cons_zero] <;> intro ho
    all_goals first
      | omega
      | exact ⟨by decide, by decide, by simp [Mma.acqAt, Mma.pq], 0, by decide⟩
      | exact ⟨by decide, by decide, by simp [Mma.acqAt, Mma.pq], 1, by decide⟩
  case mw b ld =>
    have key : ∀ b : Fin 4, 20 ≤ (Mma.Site.mw b ld).ord ∧ (Mma.Site.mw b ld).ord < 86 := by
      cases ld <;> decide
    refine ⟨(key b).1, (key b).2, ?_, ⟨b.val % 2, by omega⟩, .inr ?_⟩
    · fin_cases b <;> simp [Progress.pollO, Mma.Site.ord, Mma.acqAt, Mma.pq]
    · fin_cases b <;> rfl

/-- **The rounds done at a pipeline state** are at most the tile's. -/
theorem mma_rounds_le {d : Mma.D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hQ : Mma.RefQ p L g d.site.ord d.v (Mma.rc n) r w)
    (hF : Mma.MFits p L g d (n .shfl) (n .vote)) (hpipe : d.site.pipe = true)
    (h20 : 20 ≤ d.site.ord) (h86 : d.site.ord < 86) : ∃ R, MmaRounds p L g R ∧ r ≤ R := by
  obtain ⟨R, bal, hC, hB⟩ := Mma.bs_ref (Mma.pmid_of hpipe) hF
  refine ⟨_, ⟨R, bal, hC.1, rfl⟩, ?_⟩
  have hB' : Mma.Bs p L g d.v = Mma.Bs p L g (mmaRef p L g R bal) := hB
  by_cases h60 : d.site.ord < 60
  · have h1 := (hQ.loop ⟨h20, h60⟩).1
    rw [hB'] at h1
    omega
  · have h1 := hQ.tail ⟨by omega, by omega⟩
    rw [hB'] at h1
    omega

/-- **The time of a pipeline state** after the first block: slot `r + 1`. -/
theorem mma_time {d : Mma.D} {n : Cls → Nat} {r : Nat} (hps : d.v.ps = Mma.shAt d.site.ord r)
    (hpipe : d.site.pipe = true) (h20 : 20 ≤ d.site.ord) (h86 : d.site.ord < 86) :
    Progress.time p L g (Mma.minj p L g d n) = Progress.clk p (r + 1) (2 * d.site.ord) := by
  have h : ¬ d.site.ord < 20 := by omega
  simp only [Progress.time, Progress.roleTime, Progress.Mm.time, hpipe, ite_true,
    Progress.Mm.pipeT, h, ite_false, Progress.Mm.round_eq h20 h86 hps]

/-- **A lane of warp 12 at a poll of a P barrier**, with `r` rounds done: its time, its successful
polls of the barrier, the barrier's stage and half, and the tile's rescale rounds. -/
theorem mma_p_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hg : g < L.threads) (hg12 : Prologue.warpIndex L g = 12) {d : Mma.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hs : Progress.isPoll d.site = true) {r : Nat} {w : Bool}
    (hQ : Mma.RefQ p L g d.site.ord d.v (Mma.rc n) r w) (ho : 96 ≤ Progress.pollO r d.site) :
    (∃ R, MmaRounds p L g R ∧ r ≤ R) ∧
      Progress.clk p (r + 1) 0 ≤ Progress.time p L g (Mma.minj p L g d n) ∧
      n (.mma (.acquire (obj L g (Progress.pollO r d.site)))) = r ∧
      okPolls (obj L g (Progress.pollO r d.site)) (X.tr g) = r ∧
      ∃ st : Fin 2, Progress.pollO r d.site = 96 + 8 * st.val ∨
        Progress.pollO r d.site = 112 + 8 * st.val := by
  obtain ⟨h20, h86, hacq, hst⟩ := p_poll_place hs ho hQ.pre
  have hpipe : d.site.pipe = true := by
    revert hs
    cases d.site <;> simp [Progress.isPoll, Mma.Site.pipe]
  obtain ⟨-, hFm⟩ := Progress.mma_ref hp hX hub hg hg12 hσ
  have hn : n (.mma (.acquire (obj L g (Progress.pollO r d.site)))) = r := by
    have h1 := hQ.acq (Progress.pollO r d.site)
    rw [hacq] at h1
    exact h1
  refine ⟨mma_rounds_le hQ hFm hpipe h20 h86, ?_, hn, ?_, hst⟩
  · rw [mma_time hQ.ps hpipe h20 h86]
    unfold Progress.clk; omega
  · have h1 := count hσ (.mma (.acquire (obj L g (Progress.pollO r d.site))))
    rw [List.take_length, hn] at h1
    exact h1

end
end PTX.Kernels.TmlFa4Fwd.Proof
