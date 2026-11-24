-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.EpBcast
public import Kernels.InklingRelDecode.Proof.Interface.SvPred

@[expose] public section

/-!
# The softmax region's Tensor Memory accesses are at the warp's lanes

The softmax machine records the lane bits its broadcast of the warp index returned (`Sm.Stg.bw`)
and addresses its S load, P store and the rescale's load and store of `O` with them. The bits are
set at the broadcast (`shfl4`) and kept by every other step. From the broadcast to the end of the
iteration (`BwSite`) the state comes from the broadcast of its iteration, whose received word is
the warp index (`Lk.sm_recv`), so the recorded bits are the warp index (`sm_bw`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

theorem afterSetup_not_bw {d d' : D} (h : Sm.afterSetup L g d = some (some d')) :
    ¬ BwSite d'.site := by
  rcases Sv.afterSetup_site h with h | h <;> rw [h] <;> simp [BwSite]

/-- **One step into a `BwSite`**: from the broadcast, with the received word's lane bits, or
from a `BwSite` with the bits kept. -/
theorem next_bw {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : BwSite d.site) :
    (d0.site = .shfl4 ∧ ∃ pc m av b c recv ok, e = ⟨pc, .shfl m av b c recv ok⟩ ∧
      Raw.laneOk (g % L.block / 32) recv = some d.stg.bw) ∨
    (BwSite d0.site ∧ d.stg.bw = d0.stg.bw) := by
  obtain ⟨pc, kd⟩ := e
  by_cases h4 : d0.site = .shfl4
  · left
    refine ⟨h4, ?_⟩
    simp only [Sm.next, h4] at hn
    split at hn
    · rename_i m av b c recv ok
      refine ⟨pc, m, av, b, c, recv, ok, rfl, ?_⟩
      split at hn
      · rename_i x hx
        simp only [Option.some.injEq] at hn
        subst hn
        exact hx
      · cases hn
    · cases hn
  right
  have hb0 : ¬ BwSite d0.site → False := by
    intro hn0
    revert hn
    cases hs0 : d0.site <;> rw [hs0] at hn0 <;> simp only [BwSite, not_true_eq_false] at hn0 <;>
      simp only [hs0, not_true_eq_false] at h4 <;> simp only [Sm.next, hs0] <;> intro hn
    all_goals (repeat' split at hn)
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (exact absurd hs (afterSetup_not_bw hn))
      | (simp only [Option.some.injEq] at hn; subst hn; simp_all [BwSite])
  refine ⟨Classical.byContradiction hb0, ?_⟩
  revert hn
  cases hs0 : d0.site <;> simp only [hs0, not_true_eq_false] at h4 <;>
    simp only [Sm.next, hs0] <;> intro hn
  all_goals (repeat' split at hn)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (exact absurd hs (afterSetup_not_bw hn))
    | (simp only [Option.some.injEq] at hn; subst hn; rfl)
    | (unfold Sm.toBar20 at hn
       split at hn
       · simp only [Option.some.injEq] at hn
         subst hn
         rfl
       · cases hn)

/-- **At the sites from the S load to the end of the iteration the recorded lane bits are the
warp index.** -/
theorem sm_bw (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ k (d : D), k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.sm d))) →
      BwSite d.site → d.stg.bw = g % L.block / 32 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro d hk hσ hs
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
  · simp [SmEntry.d0, BwSite] at hs
  · rcases next_bw hn hs with ⟨hs0, pc, m, av, b, c, recv, ok, rfl, hl⟩ | ⟨hs0, hb⟩
    · have hget : X.get (g, k0) = some ⟨pc, .shfl m av b c recv ok⟩ := he
      have hr := Lk.sm_recv hpre hX hf hg hget hσ0 hs0
      have hT : g % L.block < 128 := (hf.reach hg hσ0).1
      rw [hr, Raw.laneOk_b32 (by omega)] at hl
      exact (Option.some.inj hl).symm
    · rw [hb]
      exact ih k0 (by omega) d0 (by omega) hσ0 hs0

/-- `sm_bw` without the bound on the event count. -/
theorem sm_bw' (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {d : D}
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : BwSite d.site) :
    d.stg.bw = g % L.block / 32 := by
  by_cases h : k ≤ (X.tr g).length
  · exact sm_bw hpre hX hf hg k d h hσ hs
  · exact sm_bw hpre hX hf hg _ d le_rfl ((Frame.stateAt_of_le (C := code L Q) (X := X) (g := g)
      (k := k) (by omega)).symm.trans hσ) hs

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
